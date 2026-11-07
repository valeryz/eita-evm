/-
  WorldSlotsVectors.lean — `lake exe worldSlotsVectors [ops] [seed]` prints a random op trace
  over the slot-table model (Evm.CL.WorldSlotsModel) with the model's answers; the C table
  replays it (c/test_world_slots.c, `make -C c test_world_slots_model`). One op per line,
  limbs in hex, least significant first:

    P id k0 k1 k2 k3 v0 v1 v2 v3     put
    R id k0 k1 k2 k3                 remove
    D id                             drop
    G id k0 k1 k2 k3 = 0             get: absent
    G id k0 k1 k2 k3 = 1 v0 v1 v2 v3 get: present, with the model's value
    H id = 0|1                       has a table

  Keys come from a small pool built to collide in the C hash (equal low limbs, other high
  limbs), ids from 0..15, so tables grow, hold tombstones and are dropped and re-made.
-/
import Evm.CL.WorldSlotsModel

open Evm.CL.WorldSlotsModel

def limbs (w : Word) : List Nat := (List.range 4).map fun i => (w.toNat >>> (64 * i)) % 2 ^ 64
def hex (w : Word) : String := " ".intercalate ((limbs w).map fun n => String.ofList (Nat.toDigits 16 n))
def ofLimbs (l0 l1 l2 l3 : Nat) : Word := BitVec.ofNat 256 (l0 + l1 * 2 ^ 64 + l2 * 2 ^ 128 + l3 * 2 ^ 192)

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def key (r : Nat) : Word :=
  let r := r % 400
  ofLimbs (if r % 7 = 0 then 0 else r % 29) (if r % 3 = 0 then 0 else r % 11) (r / 29)
    (if r % 5 = 1 then 2 ^ 64 - 1 else 0)

def val (r s : Nat) : Word :=
  match r % 4 with
  | 0 => 0
  | 1 => BitVec.ofNat 256 (s % 1000)
  | _ => ofLimbs s (lcg s) (lcg (lcg s)) (if r % 8 = 2 then 0 else s >>> 7)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20000
  let seed := (args[1]? >>= String.toNat?).getD 20261107
  let mut m := empty
  let mut s := seed
  let out ← IO.getStdout
  for _ in [0:n] do
    s := lcg s
    let r := s >>> 33
    let id := r % 16
    let k := key (r / 16)
    let op := (r / 7000) % 100
    if op < 50 then
      s := lcg s
      let v := val (s >>> 40) s
      m := put m id k v
      out.putStrLn s!"P {id} {hex k} {hex v}"
    else if op < 70 then
      m := remove m id k
      out.putStrLn s!"R {id} {hex k}"
    else if op < 72 then
      m := drop m id
      out.putStrLn s!"D {id}"
    else if op < 96 then
      match get m id k with
      | none => out.putStrLn s!"G {id} {hex k} = 0"
      | some v => out.putStrLn s!"G {id} {hex k} = 1 {hex v}"
    else
      out.putStrLn s!"H {id} = {if hasTable m id then 1 else 0}"
