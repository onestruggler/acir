/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Execution benchmark: the Lean decision procedure for Clifford circuits

For random circuits `w` over `H`, `S` and `CZ` on `n` wires, decides that `w`
and `w S⁴` have the same matrix, with the procedure the soundness proof of
`QCert.SelingerClifford` uses: `Sim.check`, which simulates both circuits on
every basis vector over ℤ[ω].  The circuits come from the same linear
congruential generator as `pldi/compare/bench/CliffordBench.agda`, so both
programs decide the same circuits.

Usage: `cliffordbench n L seed reps` (`n ≥ 2`) prints the number of decisions
that hold (`reps`) and the milliseconds they took, measured with the
monotonic clock inside the program.
-/
import QCert.SelingerClifford.Soundness

open QCert QCert.SelingerClifford

namespace Bench

/-- `x ↦ (1103515245 x + 12345) mod 2³¹`. -/
def next (x : Nat) : Nat := (1103515245 * x + 12345) % 2147483648

/-- A one-wire gate on wire `k`. -/
def place1 : (n k : Nat) → Gate 1 → Gen Gate n
  | _ + 1, 0, g => .gate1 g
  | n + 1, k + 1, g => .up (place1 n k g)
  | 0, _, _ => .gate0 .ω

/-- A two-wire gate on wires `k, k + 1`. -/
def place2 : (n k : Nat) → Gate 2 → Gen Gate n
  | _ + 2, 0, g => .gate2 g
  | n + 1, k + 1, g => .up (place2 n k g)
  | _, _, _ => .gate0 .ω

/-- The gate drawn from the state `c`: `H`, `S` or `CZ` by `c mod 3`, its wire
from the next state `y`. -/
def pick (n c y : Nat) : Gen Gate n :=
  match c % 3 with
  | 0 => place1 n (y % n) .H
  | 1 => place1 n (y % n) .S
  | _ => place2 n (y % (n - 1)) .CZ

def gates (n : Nat) : Nat → Nat → List (Gen Gate n)
  | 0, _ => []
  | L + 1, x => pick n (next x) (next (next x)) :: gates n L (next (next x))

def decide (n L seed : Nat) : Bool :=
  let w : Circ n := FreeMonoid.ofList (gates n L seed)
  let s4 : Circ n := FreeMonoid.ofList (List.replicate 4 (place1 n 0 .S))
  Sim.check ops 1 1 w (w * s4)

/-- The number of the decisions for the seeds `seed, …, seed + reps - 1`
that hold. -/
def count (n L seed : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => (if decide n L (seed + r) then 1 else 0) + count n L seed r

end Bench

def main (args : List String) : IO UInt32 := do
  match args with
  | [n, L, seed, reps] =>
    let t0 ← IO.monoNanosNow
    let k ← IO.lazyPure fun _ => Bench.count n.toNat! L.toNat! seed.toNat! reps.toNat!
    IO.println k
    let t1 ← IO.monoNanosNow
    IO.println ((t1 - t0) / 1000000)
    return 0
  | _ =>
    IO.println "usage: cliffordbench n L seed reps"
    return 1
