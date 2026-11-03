/*
 * uds.c — minimal Unix-domain-socket FFI for the in-process JIT emit server
 * (#235). Bound into the `emitJIT` exe via `@[extern]`; lets the Lean emitter
 * run as a persistent daemon that SBCL's replay talks to over a UDS, instead of
 * spawning a fresh process per contract. Byte framing only (no FD passing yet).
 *
 * Each function follows Lean's IO-extern ABI: the trailing lean_obj_arg is the
 * RealWorld token (ignored), and the result is wrapped in lean_io_result_mk_ok.
 * File descriptors are passed as UInt32 (-1u on error).
 */
#include <stdint.h>
#include <string.h>
#include <stddef.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <lean/lean.h>

LEAN_EXPORT lean_obj_res lean_uds_listen(b_lean_obj_arg path_obj, lean_obj_arg w) {
    (void)w;
    const char *path = lean_string_cstr(path_obj);
    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return lean_io_result_mk_ok(lean_box_uint32((uint32_t)-1));
    struct sockaddr_un addr;
    memset(&addr, 0, sizeof addr);
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, path, sizeof(addr.sun_path) - 1);
    unlink(path);
    if (bind(fd, (struct sockaddr *)&addr, sizeof addr) < 0 || listen(fd, 4) < 0) {
        close(fd);
        return lean_io_result_mk_ok(lean_box_uint32((uint32_t)-1));
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res lean_uds_accept(uint32_t lfd, lean_obj_arg w) {
    (void)w;
    int cfd = accept((int)lfd, NULL, NULL);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)cfd));
}

/* Read up to n bytes (loops over short reads); returns a ByteArray of the bytes
 * actually read — a result smaller than n means the peer closed the stream. */
LEAN_EXPORT lean_obj_res lean_fd_read(uint32_t fd, uint32_t n, lean_obj_arg w) {
    (void)w;
    lean_object *arr = lean_alloc_sarray(1, n, n);
    uint8_t *buf = lean_sarray_cptr(arr);
    size_t got = 0;
    while (got < n) {
        ssize_t r = read((int)fd, buf + got, (size_t)n - got);
        if (r <= 0) break;
        got += (size_t)r;
    }
    lean_sarray_set_size(arr, got);
    return lean_io_result_mk_ok(arr);
}

/* Write all bytes (loops over short writes); returns the count written. */
LEAN_EXPORT lean_obj_res lean_fd_write(uint32_t fd, b_lean_obj_arg ba, lean_obj_arg w) {
    (void)w;
    size_t n = lean_sarray_size(ba);
    const uint8_t *buf = lean_sarray_cptr(ba);
    size_t put = 0;
    while (put < n) {
        ssize_t r = write((int)fd, buf + put, n - put);
        if (r <= 0) break;
        put += (size_t)r;
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)put));
}

LEAN_EXPORT lean_obj_res lean_fd_close(uint32_t fd, lean_obj_arg w) {
    (void)w;
    close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}
