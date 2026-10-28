/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A fast decision procedure for circuit identities

`Sim.check` simulates circuits over ℚ(√2), whose rational arithmetic the
kernel normalises by `gcd` at every step; beyond three wires it is too slow
(an 80-gate comparison on four wires did not finish in six minutes).  Here
the same column-by-column simulation runs on integers: a vector is
`(1/√2)^k · v` with `v` over `ℤ[√2]` (pairs of integers, `Z2`) and one
exponent `k` per circuit, which only depends on the circuit (`inc`, one for
each `H` and each `CH`).  So `H` is a sum and a difference, `CH` the same on
the block where its control is `1` and a multiplication by `√2` on the
other block (`m2`, exact on `ℤ[√2]`), `Z` and `CZ` negations; no division
and no rationals, and `Int` literal arithmetic is accelerated in the
kernel.  Two circuits are compared by one Boolean (`check`): their
simulated columns, the one with the smaller exponent multiplied by the
missing power of `√2`.

`check_sound`: `check w w' = true → opsQ.eval n w = opsQ.eval n w'`, and
`sem_of_fast` carries this to the real semantics.  The proof goes through
`Sim`'s vectors (`toS`), whose gate actions are proved there to compute the
gate operators.
-/
import QCert.RealCliffordCH.Sim

namespace QCert.RealCliffordCH.Fast

open Matrix Circuit

/-! ## `ℤ[√2]` -/

/-- `a + b √2`. -/
structure Z2 where
  a : Int
  b : Int
  deriving DecidableEq

namespace Z2

def zero : Z2 := ⟨0, 0⟩
def one : Z2 := ⟨1, 0⟩
def add (x y : Z2) : Z2 := ⟨x.a + y.a, x.b + y.b⟩
def sub (x y : Z2) : Z2 := ⟨x.a - y.a, x.b - y.b⟩
def neg (x : Z2) : Z2 := ⟨-x.a, -x.b⟩
/-- Multiplication by `√2`. -/
def m2 (x : Z2) : Z2 := ⟨2 * x.b, x.a⟩

/-- The element of ℚ(√2). -/
def toQ (x : Z2) : QSqrt2 := ⟨(x.a : ℚ), (x.b : ℚ)⟩

theorem toQ_zero : toQ zero = 0 := by ext <;> simp [toQ, zero]
theorem toQ_one : toQ one = 1 := by ext <;> simp [toQ, one]
theorem toQ_add (x y : Z2) : toQ (add x y) = toQ x + toQ y := by ext <;> simp [toQ, add]
theorem toQ_sub (x y : Z2) : toQ (sub x y) = toQ x - toQ y := by ext <;> simp [toQ, sub]
theorem toQ_neg (x : Z2) : toQ (neg x) = -toQ x := by ext <;> simp [toQ, neg]
theorem toQ_m2 (x : Z2) : toQ (m2 x) = Quadratic.X * toQ x := by
  ext <;> simp [toQ, m2, Quadratic.X]

end Z2

/-- `√2 · (1/√2) = 1` in ℚ(√2). -/
theorem X_mul_inv : (Quadratic.X : QSqrt2) * QSqrt2.invSqrt2 = 1 := by
  ext <;> simp [Quadratic.X, QSqrt2.invSqrt2]

/-! ## Vectors -/

/-- Vectors on `n` wires over `ℤ[√2]`, as nested pairs (as `Sim.Vec`). -/
@[reducible] def V : ℕ → Type
  | 0 => Z2
  | n + 1 => V n × V n

def vzero : (n : ℕ) → V n
  | 0 => Z2.zero
  | n + 1 => (vzero n, vzero n)

def vadd : {n : ℕ} → V n → V n → V n
  | 0, a, b => Z2.add a b
  | _ + 1, a, b => (vadd a.1 b.1, vadd a.2 b.2)

def vsub : {n : ℕ} → V n → V n → V n
  | 0, a, b => Z2.sub a b
  | _ + 1, a, b => (vsub a.1 b.1, vsub a.2 b.2)

def vneg : {n : ℕ} → V n → V n
  | 0, a => Z2.neg a
  | _ + 1, a => (vneg a.1, vneg a.2)

def vm2 : {n : ℕ} → V n → V n
  | 0, a => Z2.m2 a
  | _ + 1, a => (vm2 a.1, vm2 a.2)

/-- Multiplication by `√2 ^ d`. -/
def vscale : ℕ → {n : ℕ} → V n → V n
  | 0, _, v => v
  | d + 1, _, v => vm2 (vscale d v)

def vbeq : {n : ℕ} → V n → V n → Bool
  | 0, a, b => decide (a = b)
  | _ + 1, a, b => vbeq a.1 b.1 && vbeq a.2 b.2

def basisV : {n : ℕ} → State 2 n → V n
  | 0, _ => Z2.one
  | n + 1, t => if t 0 = 0 then (basisV (Fin.tail t), vzero n) else (vzero n, basisV (Fin.tail t))

/-- The vector over ℚ(√2). -/
def toS : {n : ℕ} → V n → Sim.Vec n
  | 0, a => Z2.toQ a
  | _ + 1, a => (toS a.1, toS a.2)

theorem vbeq_eq : ∀ {n : ℕ} {a b : V n}, vbeq a b = true → a = b
  | 0, a, b, h => of_decide_eq_true h
  | _ + 1, a, b, h => by
    simp only [vbeq, Bool.and_eq_true] at h
    exact Prod.ext (vbeq_eq h.1) (vbeq_eq h.2)

/-! ## Gates -/

section Gates

variable {n : ℕ}

def actH (v : V (n + 1)) : V (n + 1) := (vadd v.1 v.2, vsub v.1 v.2)
def actZ (v : V (n + 1)) : V (n + 1) := (v.1, vneg v.2)
def actCZ (v : V (n + 2)) : V (n + 2) := ((v.1.1, v.1.2), (v.2.1, vneg v.2.2))
def actCH (v : V (n + 2)) : V (n + 2) :=
  ((vm2 v.1.1, vadd v.1.2 v.2.2), (vm2 v.2.1, vsub v.1.2 v.2.2))

end Gates

/-- The action of a generator, up to the factor `√2 ^ inc g`. -/
def act : {n : ℕ} → Gen Gate n → V n → V n
  | _, .gate0 g, _ => nomatch g
  | _, .gate1 .H, v => actH v
  | _, .gate1 .Z, v => actZ v
  | _, .gate2 .CZ, v => actCZ v
  | _, .gate2 .CH, v => actCH v
  | _, .gate3 g, _ => nomatch g
  | _, .up g, v => (act g v.1, act g v.2)

/-- The power of `√2` a generator's integer action carries. -/
def inc : {n : ℕ} → Gen Gate n → ℕ
  | _, .gate0 _ => 0
  | _, .gate1 .H => 1
  | _, .gate1 .Z => 0
  | _, .gate2 .CZ => 0
  | _, .gate2 .CH => 1
  | _, .gate3 _ => 0
  | _, .up g => inc g

/-- The action of a circuit, in operator order. -/
def actW {n : ℕ} (w : Circ n) (v : V n) : V n := w.toList.foldr act v

/-- The power of `√2` a circuit's integer action carries. -/
def incW {n : ℕ} (w : Circ n) : ℕ := (w.toList.map inc).sum

/-- Two circuits have the same operator: their integer simulations agree on
every basis vector once brought to the same power of `√2`. -/
def check {n : ℕ} (w w' : Circ n) : Bool :=
  let k := incW w
  let k' := incW w'
  (Sim.allStates n).all fun t =>
    vbeq (vscale (k' - k) (actW w (basisV t))) (vscale (k - k') (actW w' (basisV t)))

/-! ## Soundness -/

section Sound

open Sim

variable {n : ℕ}

local notation "√2" => (Quadratic.X : QSqrt2)

theorem tf_add : ∀ {n : ℕ} (u v : V n), toFun (toS (vadd u v)) = toFun (toS u) + toFun (toS v)
  | 0, _, _ => by funext s; simp [toFun, toS, vadd, Z2.toQ_add]
  | _ + 1, u, v => by
    funext s; simp only [toFun, toS, vadd, Pi.add_apply]
    split_ifs <;> rw [tf_add] <;> rfl

theorem tf_sub : ∀ {n : ℕ} (u v : V n), toFun (toS (vsub u v)) = toFun (toS u) - toFun (toS v)
  | 0, _, _ => by funext s; simp [toFun, toS, vsub, Z2.toQ_sub]
  | _ + 1, u, v => by
    funext s; simp only [toFun, toS, vsub, Pi.sub_apply]
    split_ifs <;> rw [tf_sub] <;> rfl

theorem tf_neg : ∀ {n : ℕ} (u : V n), toFun (toS (vneg u)) = -toFun (toS u)
  | 0, _ => by funext s; simp [toFun, toS, vneg, Z2.toQ_neg]
  | _ + 1, u => by
    funext s; simp only [toFun, toS, vneg, Pi.neg_apply]
    split_ifs <;> rw [tf_neg] <;> rfl

theorem tf_m2 : ∀ {n : ℕ} (u : V n), toFun (toS (vm2 u)) = √2 • toFun (toS u)
  | 0, _ => by funext s; simp [toFun, toS, vm2, Z2.toQ_m2]
  | _ + 1, u => by
    funext s; simp only [toFun, toS, vm2, Pi.smul_apply]
    split_ifs <;> rw [tf_m2] <;> rfl

theorem tf_scale (d : ℕ) {n : ℕ} (u : V n) : toFun (toS (vscale d u)) = √2 ^ d • toFun (toS u) := by
  induction d with
  | zero => rw [vscale, pow_zero, one_smul]
  | succ d ih => rw [vscale, tf_m2, ih, smul_smul, pow_succ, mul_comm]

theorem tf_pair (a b : V n) (s : State 2 (n + 1)) :
    toFun (toS ((a, b) : V (n + 1))) s =
      if s 0 = 0 then toFun (toS a) (Fin.tail s) else toFun (toS b) (Fin.tail s) :=
  Sim.toFun_pair _ _ s


theorem tf_pair2 (a b c d : V n) (s : State 2 (n + 2)) :
    toFun (toS (((a, b), (c, d)) : V (n + 2))) s =
      if s 0 = 0 then (if s 1 = 0 then toFun (toS a) (Fin.tail (Fin.tail s))
        else toFun (toS b) (Fin.tail (Fin.tail s)))
      else (if s 1 = 0 then toFun (toS c) (Fin.tail (Fin.tail s))
        else toFun (toS d) (Fin.tail (Fin.tail s))) :=
  Sim.toFun_pair2 _ _ _ _ s

theorem toS_zero : ∀ n, toS (vzero n) = Sim.zero n
  | 0 => Z2.toQ_zero
  | n + 1 => by simp only [toS, vzero, Sim.zero, toS_zero n]

theorem toS_basis : ∀ {n : ℕ} (t : State 2 n), toS (basisV t) = Sim.basis t
  | 0, _ => Z2.toQ_one
  | n + 1, t => by
    simp only [basisV, Sim.basis]
    split_ifs <;> simp only [toS, toS_zero, toS_basis]

/-- One gate: the integer action is `√2 ^ inc g` times `Sim`'s. -/
theorem tf_act : ∀ {n : ℕ} (g : Gen Gate n) (v : V n),
    toFun (toS (act g v)) = √2 ^ inc g • toFun (Sim.act g (toS v))
  | _, .gate0 g, _ => nomatch g
  | _, .gate1 .H, v => by
    funext s
    simp only [act, actH, inc, Sim.act, Sim.actH, pow_one, Pi.smul_apply, smul_eq_mul]
    rw [tf_pair, Sim.toFun_pair]
    split_ifs
    · rw [Sim.toFun_smul_apply, tf_add, Sim.toFun_add_apply, ← mul_assoc, X_mul_inv, one_mul]
      simp only [Pi.add_apply]; rfl
    · rw [Sim.toFun_smul_apply, tf_sub, Sim.toFun_sub_apply, ← mul_assoc, X_mul_inv, one_mul]
      simp only [Pi.sub_apply]; rfl
  | _, .gate1 .Z, v => by
    funext s
    simp only [act, actZ, inc, Sim.act, Sim.actZ, pow_zero, one_smul]
    rw [tf_pair, Sim.toFun_pair]
    split_ifs
    · rfl
    · rw [tf_neg, Sim.toFun_neg_apply]; rfl
  | _, .gate2 .CZ, v => by
    funext s
    simp only [act, actCZ, inc, Sim.act, Sim.actCZ, pow_zero, one_smul]
    rw [tf_pair2, Sim.toFun_pair2]
    split_ifs
    · rfl
    · rfl
    · rfl
    · rw [tf_neg, Sim.toFun_neg_apply]; rfl
  | _, .gate2 .CH, v => by
    funext s
    simp only [act, actCH, inc, Sim.act, Sim.actCH, pow_one, Pi.smul_apply, smul_eq_mul]
    rw [tf_pair2, Sim.toFun_pair2]
    split_ifs
    · rw [tf_m2]; rfl
    · rw [tf_add, Sim.toFun_smul_apply, Sim.toFun_add_apply, ← mul_assoc, X_mul_inv, one_mul]
      rfl
    · rw [tf_m2]; rfl
    · rw [tf_sub, Sim.toFun_smul_apply, Sim.toFun_sub_apply, ← mul_assoc, X_mul_inv, one_mul]
      rfl
  | _, .gate3 g, _ => nomatch g
  | _, .up g, v => by
    funext s
    simp only [act, inc, Sim.act, Pi.smul_apply, smul_eq_mul]
    rw [tf_pair, show toS v = (toS v.1, toS v.2) from rfl, Sim.toFun_pair]
    split_ifs
    · rw [tf_act g v.1]; rfl
    · rw [tf_act g v.2]; rfl

theorem tf_gen (g : Gen Gate n) (v : V n) :
    toFun (toS (act g v)) = √2 ^ inc g • (opsQ.gen g *ᵥ toFun (toS v)) := by
  rw [tf_act, Sim.gen_mulVec]

theorem tf_actW (w : Circ n) (v : V n) :
    toFun (toS (actW w v)) = √2 ^ incW w • (opsQ.eval n w *ᵥ toFun (toS v)) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [map_one, one_mulVec]
    simp only [actW, incW, FreeMonoid.toList_one, List.foldr_nil, List.map_nil, List.sum_nil,
      pow_zero, one_smul]
  | mul_of g w ih =>
    show toFun (toS (act g (actW w v))) = _
    rw [tf_gen, ih, mulVec_smul, smul_smul, map_mul, ← mulVec_mulVec]
    have : incW (FreeMonoid.of g * w) = inc g + incW w := by simp [incW]
    rw [this, pow_add]
    rfl

theorem pow_cancel {d : ℕ} {f g : State 2 n → QSqrt2} (h : √2 ^ d • f = √2 ^ d • g) : f = g := by
  have e : (QSqrt2.invSqrt2 ^ d * √2 ^ d) = 1 := by
    rw [← mul_pow, mul_comm, X_mul_inv, one_pow]
  have := congrArg (fun F => QSqrt2.invSqrt2 ^ d • F) h
  simpa only [smul_smul, e, one_smul] using this

/-- Soundness of `check`. -/
theorem check_sound {w w' : Circ n} (h : check w w' = true) : opsQ.eval n w = opsQ.eval n w' := by
  funext s t
  rw [check, List.all_eq_true] at h
  have ht := vbeq_eq (h t (Sim.mem_allStates t))
  have hf : toFun (toS (vscale (incW w' - incW w) (actW w (basisV t)))) =
      toFun (toS (vscale (incW w - incW w') (actW w' (basisV t)))) := by rw [ht]
  rw [tf_scale, tf_scale, tf_actW, tf_actW, toS_basis, Sim.toFun_basis, smul_smul, smul_smul,
    ← pow_add, ← pow_add] at hf
  have e : incW w' - incW w + incW w = incW w - incW w' + incW w' := by omega
  rw [e] at hf
  have hc := congrFun (pow_cancel hf) s
  simpa only [mulVec_single_one, transpose_apply] using hc

/-- An identity decided by `check` holds in the semantics. -/
theorem sem_of_fast {w w' : Circ n} (h : check w w' = true) : S.sem n w = S.sem n w' :=
  S.sem_eq_of_eval QSqrt2.toR opsQ toOps_eq (check_sound h)

end Sound

end QCert.RealCliffordCH.Fast
