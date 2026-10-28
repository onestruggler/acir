/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Idle wires on top

A derivation on `k` wires is a derivation on the bottom `k` of `n + k`
wires (`derives_pad`): each rule, padded, is a padded rule, and each
structural rule, padded, is the same structural rule.  The rules are
padded by `n + m` where they were padded by `m`; the two widths
`n + (m + j)` and `n + m + j` are equal but not definitionally, so the
circuits are compared up to `HEq`.
-/
import QCert.QuditClifford.Group

namespace QCert.QuditClifford

open Circuit

section HEq

variable {Gate : ℕ → Type}

theorem gate0_heq {a b : ℕ} (h : a = b) (c : Gate 0) :
    HEq (Gen.gate0 (n := a) c) (Gen.gate0 (n := b) c) := by subst h; rfl

theorem gate1_heq {a b : ℕ} (h : a = b) (c : Gate 1) :
    HEq (Gen.gate1 (n := a) c) (Gen.gate1 (n := b) c) := by subst h; rfl

theorem gate2_heq {a b : ℕ} (h : a = b) (c : Gate 2) :
    HEq (Gen.gate2 (n := a) c) (Gen.gate2 (n := b) c) := by subst h; rfl

theorem gate3_heq {a b : ℕ} (h : a = b) (c : Gate 3) :
    HEq (Gen.gate3 (n := a) c) (Gen.gate3 (n := b) c) := by subst h; rfl

theorem up_heq {a b : ℕ} (h : a = b) {x : Gen Gate a} {y : Gen Gate b} (hxy : HEq x y) :
    HEq (Gen.up x) (Gen.up y) := by subst h; cases hxy; rfl

/-- Padding twice is padding once, up to the associativity of the widths. -/
theorem Gen.pad_pad_heq (n m : ℕ) : {k : ℕ} → (x : Gen Gate k) →
    HEq (Gen.pad n (Gen.pad m x)) (Gen.pad (n + m) x)
  | _, .gate0 c => gate0_heq (Nat.add_assoc _ _ _).symm c
  | _, .gate1 c => gate1_heq (Nat.add_assoc _ _ _).symm c
  | _, .gate2 c => gate2_heq (Nat.add_assoc _ _ _).symm c
  | _, .gate3 c => gate3_heq (Nat.add_assoc _ _ _).symm c
  | _, .up x => up_heq (Nat.add_assoc _ _ _).symm (Gen.pad_pad_heq n m x)

theorem map_heq {k a b : ℕ} (h : a = b) {f : Gen Gate k → Gen Gate a} {f' : Gen Gate k → Gen Gate b}
    (hf : ∀ x, HEq (f x) (f' x)) (w : Circuit Gate k) :
    HEq (FreeMonoid.map f w) (FreeMonoid.map f' w) := by
  subst h
  have : f = f' := funext fun x => eq_of_heq (hf x)
  subst this; rfl

theorem pad_pad_heq (n m : ℕ) {k : ℕ} (w : Circuit Gate k) :
    HEq (Circuit.pad n (Circuit.pad m w)) (Circuit.pad (n + m) w) := by
  show HEq (FreeMonoid.map (Gen.pad n) (FreeMonoid.map (Gen.pad m) w)) _
  rw [FreeMonoid.map_map]
  exact map_heq (Nat.add_assoc _ _ _).symm (fun x => Gen.pad_pad_heq n m x) w

theorem pad_shift (n : ℕ) {k : ℕ} (w : Circuit Gate k) :
    Circuit.pad n (Circuit.shift w) = Circuit.shift (Circuit.pad n w) := by
  show FreeMonoid.map (Gen.pad n) (FreeMonoid.map Gen.up w) =
    FreeMonoid.map Gen.up (FreeMonoid.map (Gen.pad n) w)
  rw [FreeMonoid.map_map, FreeMonoid.map_map]; rfl

end HEq

variable (p : ℕ) [hp : Fact p.Prime] (g : ZMod p)

theorem derives_heq {a b : ℕ} (h : a = b) {w v : Circ a} {w' v' : Circ b} (hw : HEq w w')
    (hv : HEq v v') (d : Derives (Padded (Rule p g)) a w v) : Derives (Padded (Rule p g)) b w' v' := by
  subst h; cases hw; cases hv; exact d

/-- Every equation of the theory on `k` wires holds on the bottom `k` of
`n + k` wires. -/
theorem theory_pad (n : ℕ) {k : ℕ} {w v : Circ k} (h : Theory p g k w v) :
    Derives (Padded (Rule p g)) (n + k) (Circuit.pad n w) (Circuit.pad n v) := by
  induction h with
  | rule hr =>
    cases hr with
    | @pad j m w' v' hb =>
      exact derives_heq p g (Nat.add_assoc n m j) (pad_pad_heq n m w').symm
        (pad_pad_heq n m v').symm (derives_rule p g (n := n + m) hb)
  | shift _ ih =>
    rw [pad_shift, pad_shift]; exact derives_shift p g ih
  | comm1 c y =>
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm1 c (Gen.pad n y))
  | comm2 c y =>
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm2 c (Gen.pad n y))
  | comm3 c y =>
    simp only [map_mul, Circuit.pad, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm3 c (Gen.pad n y))
  | scalar c =>
    simp only [Circuit.pad, FreeMonoid.map_of]
    exact Derivable.of (Lift.scalar (n := n + _) c)

/-- Every derivation on `k` wires is a derivation on the bottom `k` of
`n + k` wires. -/
theorem derives_pad (n : ℕ) {k : ℕ} {w v : Circ k} (h : Derives (Padded (Rule p g)) k w v) :
    Derives (Padded (Rule p g)) (n + k) (Circuit.pad n w) (Circuit.pad n v) := by
  have : conGen (Theory p g k) ≤
      (conGen (Theory p g (n + k))).comap (Circuit.pad n) (map_mul _) :=
    Con.conGen_le fun a b hab => theory_pad p g n hab
  exact this h

theorem le_ker_pad (n k : ℕ) : Cn p g k ≤ Con.ker ((mk p g (n + k)).comp (Circuit.pad n)) :=
  Con.conGen_le fun _ _ h => (Con.ker_rel _).2 (by
    show mk p g (n + k) (Circuit.pad n _) = mk p g (n + k) (Circuit.pad n _)
    exact mk_eq_mk.2 (derives_pad p g n (Derivable.of h)))

/-- A class of `k`-wire circuits on the bottom `k` of `n + k` wires. -/
def padG (n k : ℕ) : CG p g k →* CG p g (n + k) :=
  (Cn p g k).lift ((mk p g (n + k)).comp (Circuit.pad n)) (le_ker_pad p g n k)

@[simp] theorem padG_mk (n : ℕ) {k : ℕ} (w : Circ k) :
    padG p g n k (mk p g k w) = mk p g (n + k) (Circuit.pad n w) := rfl

end QCert.QuditClifford
