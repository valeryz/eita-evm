//! eita-engine-api — the Engine API edge of `eita engine` (src/engine/engine.lisp): HTTP and
//! JWT for a consensus client, each JSON-RPC call forwarded to the engine over its local socket.
//!
//!   eita-engine-api --listen 127.0.0.1:8551 --jwt FILE --socket STATE/engine.sock [--parent PID]
//!
//! `eita engine` starts it (docs/run-a-node.md). This side owns only the transport: the HTTP
//! listener, JWT (authentication.md: HS256 with the 32-byte hex secret in FILE, mode 0600;
//! `iat` within ±60 s; no file, no listener), the JSON-RPC envelope (id, batches, -32700 /
//! -32600), and a hard 10 s bound per call. Every method, its parameters and every verdict are
//! the engine's: a call goes over the socket as a 4-byte big-endian length and UTF-8 JSON
//! {"method","params"}, and comes back the same way as {"result"} or {"error"}. The engine
//! answers within 7 s (SYNCING past that). With --parent PID it exits once process PID is no
//! longer its parent.

use axum::body::Bytes;
use axum::extract::{DefaultBodyLimit, State};
use axum::http::{header, HeaderMap, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::post;
use axum::Router;
use base64::Engine as _;
use hmac::{Hmac, Mac};
use serde_json::{json, Value};
use sha2::Sha256;
use std::path::{Path, PathBuf};
use std::process::exit;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

struct Engine {
    secret: [u8; 32],
    socket: PathBuf,
}

const CALL_TIMEOUT: Duration = Duration::from_secs(10);
const IAT_WINDOW: i64 = 60;
const MAX_BODY: usize = 64 << 20;

/// The JWT secret: a file of 32 hex bytes (an optional 0x), readable by its owner only.
fn load_secret(path: &Path) -> Result<[u8; 32], String> {
    let meta = std::fs::metadata(path).map_err(|e| format!("{}: {e}: the engine port stays closed", path.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = meta.permissions().mode() & 0o777;
        if mode & 0o077 != 0 {
            return Err(format!("{} has mode {mode:o}: it must be 0600", path.display()));
        }
    }
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let hex = text.trim().trim_start_matches("0x");
    if hex.len() != 64 || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(format!("{}: not a 32-byte hex secret", path.display()));
    }
    let mut s = [0u8; 32];
    for (i, b) in s.iter_mut().enumerate() {
        *b = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap();
    }
    Ok(s)
}

fn now() -> i64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs() as i64).unwrap_or(0)
}

/// `Authorization: Bearer <jwt>` is a token the secret signed (HS256 only) issued within ±60 s
/// of NOW. Err: why not (logged, never echoed with the token).
fn check_jwt(secret: &[u8; 32], auth: Option<&str>, now: i64) -> Result<(), &'static str> {
    let tok = auth.and_then(|a| a.strip_prefix("Bearer ")).ok_or("no bearer token")?;
    let mut parts = tok.split('.');
    let (Some(h), Some(c), Some(s), None) = (parts.next(), parts.next(), parts.next(), parts.next()) else {
        return Err("not a JWT");
    };
    let b64 = base64::engine::general_purpose::URL_SAFE_NO_PAD;
    let hdr: Value = b64.decode(h).ok().and_then(|b| serde_json::from_slice(&b).ok()).ok_or("bad JWT header")?;
    if hdr.get("alg").and_then(Value::as_str) != Some("HS256") {
        return Err("JWT alg is not HS256");
    }
    let sig = b64.decode(s).map_err(|_| "bad JWT signature encoding")?;
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).expect("any key length");
    mac.update(&tok.as_bytes()[..h.len() + 1 + c.len()]);
    mac.verify_slice(&sig).map_err(|_| "JWT signature does not verify")?;
    let claims: Value = b64.decode(c).ok().and_then(|b| serde_json::from_slice(&b).ok()).ok_or("bad JWT claims")?;
    let iat = claims.get("iat").and_then(Value::as_i64).ok_or("JWT has no iat")?;
    if (now - iat).abs() > IAT_WINDOW {
        return Err("JWT iat is not within 60 s of now");
    }
    Ok(())
}

/// One call over the replay's socket: its {"result"} or {"error"} object.
async fn forward(socket: &Path, method: &str, params: &Value) -> Value {
    let call = async {
        let mut s = tokio::net::UnixStream::connect(socket).await?;
        let body = serde_json::to_vec(&json!({"method": method, "params": params})).unwrap();
        s.write_all(&(body.len() as u32).to_be_bytes()).await?;
        s.write_all(&body).await?;
        let mut len = [0u8; 4];
        s.read_exact(&mut len).await?;
        let mut buf = vec![0u8; u32::from_be_bytes(len) as usize];
        s.read_exact(&mut buf).await?;
        Ok::<Vec<u8>, std::io::Error>(buf)
    };
    match tokio::time::timeout(CALL_TIMEOUT, call).await {
        Ok(Ok(buf)) => serde_json::from_slice(&buf)
            .unwrap_or_else(|_| json!({"error": {"code": -32603, "message": "Internal error: the engine's reply is not JSON"}})),
        Ok(Err(e)) => json!({"error": {"code": -32603, "message": format!("Internal error: the engine is not reachable ({e})")}}),
        Err(_) => json!({"error": {"code": -32603, "message": "Internal error: no answer from the engine in 10 s"}}),
    }
}

async fn call(engine: &Engine, req: &Value) -> Value {
    let id = req.get("id").cloned().unwrap_or(Value::Null);
    let method = req.get("method").and_then(Value::as_str);
    let params = req.get("params").cloned().unwrap_or(json!([]));
    let (Some(method), true, true) = (method, req.get("jsonrpc") == Some(&json!("2.0")), params.is_array()) else {
        return json!({"jsonrpc": "2.0", "id": id, "error": {"code": -32600, "message": "Invalid request"}});
    };
    let mut out = forward(&engine.socket, method, &params).await;
    let mut reply = json!({"jsonrpc": "2.0", "id": id});
    match out.get_mut("error") {
        Some(e) => reply["error"] = e.take(),
        None => reply["result"] = out.get_mut("result").map(Value::take).unwrap_or(Value::Null),
    }
    reply
}

async fn handle(State(engine): State<Arc<Engine>>, headers: HeaderMap, body: Bytes) -> Response {
    let auth = headers.get(header::AUTHORIZATION).and_then(|v| v.to_str().ok());
    if let Err(why) = check_jwt(&engine.secret, auth, now()) {
        eprintln!("eita-engine-api: request refused: {why}");
        return (StatusCode::UNAUTHORIZED, [(header::CONTENT_TYPE, "application/json")], format!("{{\"error\":\"{why}\"}}")).into_response();
    }
    let reply = match serde_json::from_slice::<Value>(&body) {
        Err(_) => json!({"jsonrpc": "2.0", "id": null, "error": {"code": -32700, "message": "Parse error"}}),
        Ok(Value::Array(calls)) if !calls.is_empty() => {
            let mut out = Vec::with_capacity(calls.len());
            for c in &calls {
                out.push(call(&engine, c).await);
            }
            Value::Array(out)
        }
        Ok(req) if req.is_object() => call(&engine, &req).await,
        Ok(_) => json!({"jsonrpc": "2.0", "id": null, "error": {"code": -32600, "message": "Invalid request"}}),
    };
    ([(header::CONTENT_TYPE, "application/json")], reply.to_string()).into_response()
}

fn router(secret: [u8; 32], socket: PathBuf) -> Router {
    Router::new()
        .route("/", post(handle))
        .layer(DefaultBodyLimit::max(MAX_BODY))
        .with_state(Arc::new(Engine { secret, socket }))
}

/// Serve the Engine API on LISTEN until the process ends; refuse to start without a secret.
async fn serve(listen: &str, jwt: &Path, socket: PathBuf) {
    let secret = load_secret(jwt).unwrap_or_else(|e| {
        eprintln!("eita-engine-api: {e}");
        exit(2)
    });
    let listener = tokio::net::TcpListener::bind(listen).await.unwrap_or_else(|e| {
        eprintln!("eita-engine-api: {listen}: {e}");
        exit(2)
    });
    eprintln!("eita-engine-api: Engine API on http://{listen}/ (JWT), calls to {}", socket.display());
    axum::serve(listener, router(secret, socket)).await.unwrap();
}

/// Exit once process PID is no longer the parent (it ended; this process was reparented).
fn exit_with_parent(pid: u32) {
    std::thread::spawn(move || loop {
        if std::os::unix::process::parent_id() != pid {
            exit(3);
        }
        std::thread::sleep(Duration::from_secs(1));
    });
}

#[tokio::main]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    let opt = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1)).cloned();
    let (Some(listen), Some(jwt), Some(socket)) = (opt("--listen"), opt("--jwt"), opt("--socket")) else {
        eprintln!("usage: eita-engine-api --listen ADDR --jwt FILE --socket PATH [--parent PID]");
        exit(2)
    };
    if let Some(pid) = opt("--parent") {
        exit_with_parent(pid.parse().unwrap_or_else(|_| {
            eprintln!("eita-engine-api: --parent {pid}: not a process id");
            exit(2)
        }));
    }
    serve(&listen, Path::new(&jwt), PathBuf::from(socket)).await;
}

#[cfg(test)]
mod tests {
    use super::*;
    use tower::ServiceExt;

    const KEY: [u8; 32] = [7u8; 32];

    fn token(key: &[u8], alg: &str, iat: i64) -> String {
        let b64 = base64::engine::general_purpose::URL_SAFE_NO_PAD;
        let h = b64.encode(format!("{{\"alg\":\"{alg}\",\"typ\":\"JWT\"}}"));
        let c = b64.encode(format!("{{\"iat\":{iat}}}"));
        let mut mac = Hmac::<Sha256>::new_from_slice(key).unwrap();
        mac.update(format!("{h}.{c}").as_bytes());
        format!("Bearer {h}.{c}.{}", b64.encode(mac.finalize().into_bytes()))
    }

    #[test]
    fn jwt_rules() {
        let t = 1_800_000_000;
        assert!(check_jwt(&KEY, Some(&token(&KEY, "HS256", t)), t).is_ok());
        assert!(check_jwt(&KEY, Some(&token(&KEY, "HS256", t - 60)), t).is_ok());
        assert!(check_jwt(&KEY, Some(&token(&KEY, "HS256", t + 60)), t).is_ok());
        assert_eq!(check_jwt(&KEY, Some(&token(&KEY, "HS256", t - 61)), t), Err("JWT iat is not within 60 s of now"));
        assert_eq!(check_jwt(&KEY, Some(&token(&KEY, "HS256", t + 61)), t), Err("JWT iat is not within 60 s of now"));
        assert_eq!(check_jwt(&KEY, Some(&token(&[8u8; 32], "HS256", t)), t), Err("JWT signature does not verify"));
        assert_eq!(check_jwt(&KEY, Some(&token(&KEY, "none", t)), t), Err("JWT alg is not HS256"));
        assert_eq!(check_jwt(&KEY, None, t), Err("no bearer token"));
        assert_eq!(check_jwt(&KEY, Some("Bearer abc"), t), Err("not a JWT"));
        // alg none with an empty signature: refused before the signature
        let b64 = base64::engine::general_purpose::URL_SAFE_NO_PAD;
        let unsigned = format!("Bearer {}.{}.", b64.encode("{\"alg\":\"none\"}"), b64.encode(format!("{{\"iat\":{t}}}")));
        assert!(check_jwt(&KEY, Some(&unsigned), t).is_err());
    }

    #[test]
    fn secret_file_rules() {
        use std::os::unix::fs::PermissionsExt;
        let dir = std::env::temp_dir().join(format!("eita-jwt-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("jwt.hex");
        std::fs::write(&f, format!("0x{}\n", "07".repeat(32))).unwrap();
        std::fs::set_permissions(&f, std::fs::Permissions::from_mode(0o644)).unwrap();
        assert!(load_secret(&f).unwrap_err().contains("must be 0600"));
        std::fs::set_permissions(&f, std::fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(load_secret(&f).unwrap(), KEY);
        std::fs::write(&f, "abcd").unwrap();
        assert!(load_secret(&f).unwrap_err().contains("not a 32-byte hex secret"));
        assert!(load_secret(&dir.join("none")).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// The envelope over a stand-in replay socket: the id comes back, a batch is answered in
    /// order, an error stays an error, a bad token is a 401 that never reaches the socket.
    #[tokio::test]
    async fn forwards_calls() {
        let sock = std::env::temp_dir().join(format!("eita-engine-test-{}.sock", std::process::id()));
        let _ = std::fs::remove_file(&sock);
        let l = tokio::net::UnixListener::bind(&sock).unwrap();
        tokio::spawn(async move {
            loop {
                let (mut s, _) = l.accept().await.unwrap();
                let mut len = [0u8; 4];
                s.read_exact(&mut len).await.unwrap();
                let mut buf = vec![0u8; u32::from_be_bytes(len) as usize];
                s.read_exact(&mut buf).await.unwrap();
                let req: Value = serde_json::from_slice(&buf).unwrap();
                let out = if req["method"] == "eth_chainId" { json!({"result": "0x1"}) } else { json!({"error": {"code": -32601, "message": "Method not found"}}) };
                let b = out.to_string().into_bytes();
                s.write_all(&(b.len() as u32).to_be_bytes()).await.unwrap();
                s.write_all(&b).await.unwrap();
            }
        });
        let app = router(KEY, sock.clone());
        let post = |body: &str, auth: String| {
            axum::http::Request::post("/").header("authorization", auth).header("content-type", "application/json")
                .body(axum::body::Body::from(body.to_string())).unwrap()
        };
        let read = |r: Response| async move {
            let b = http_body_util::BodyExt::collect(r.into_body()).await.unwrap().to_bytes();
            serde_json::from_slice::<Value>(&b).unwrap()
        };
        let r = app.clone().oneshot(post(r#"{"jsonrpc":"2.0","id":7,"method":"eth_chainId","params":[]}"#, token(&KEY, "HS256", now()))).await.unwrap();
        assert_eq!(r.status(), StatusCode::OK);
        assert_eq!(read(r).await, json!({"jsonrpc": "2.0", "id": 7, "result": "0x1"}));
        let r = app.clone().oneshot(post(r#"[{"jsonrpc":"2.0","id":1,"method":"eth_chainId"},{"jsonrpc":"2.0","id":2,"method":"engine_getPayloadV5","params":[]}]"#, token(&KEY, "HS256", now()))).await.unwrap();
        let v = read(r).await;
        assert_eq!(v[0]["result"], "0x1");
        assert_eq!(v[1]["error"]["code"], -32601);
        let r = app.clone().oneshot(post("{not json", token(&KEY, "HS256", now()))).await.unwrap();
        assert_eq!(read(r).await["error"]["code"], -32700);
        let r = app.clone().oneshot(post(r#"{"id":1,"method":"eth_chainId"}"#, token(&KEY, "HS256", now()))).await.unwrap();
        assert_eq!(read(r).await["error"]["code"], -32600);
        let r = app.clone().oneshot(post(r#"{"jsonrpc":"2.0","id":1,"method":"eth_chainId"}"#, token(&KEY, "HS256", now() - 3600))).await.unwrap();
        assert_eq!(r.status(), StatusCode::UNAUTHORIZED);
        let _ = std::fs::remove_file(&sock);
    }
}
