/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Identities of level matrices over `ℚ(ω)`, decided on integer tables

`decide +kernel` on an equation between products of one- and two-level
matrices over `ℚ(ω)` (`Matrix (Fin m) (Fin m) QOmega`) makes the kernel
evaluate every entry of a product through `Finset.sum`, the two auxiliary
products of `levelMat` and `ℚ` arithmetic, and recompute every sub-product
for every entry (a chain of `k` factors costs `m ^ (k - 1)` evaluations of
each letter per entry): the twenty checks of `QCert.Greylyn.Soundness`
cost 26 s of kernel time in a lone run, the nineteen of
`QCert.BianSelingerUn.Soundness` 27 s.

Here a product is evaluated once, on a table (`FM`, a list of rows) of
elements of `ℤ[ω]` (`ZW`, four integer coefficients), every letter scaled
by `2` so that the entries stay integral (`eval e` is `2 ^ scale e` times
the matrix of `e`), and the two sides of an identity are compared at a
common scale by one Boolean (`MExpr.check`), whose soundness
(`MExpr.check_sound`) is proved once.  The tactic `level_check` reifies a
goal `A = B` into the expression language `MExpr` (`twoLevel`, `oneLevel`,
`1`, `*`, `^`) and closes it by `decide +kernel` on the Boolean: each of
the twenty checks takes tens of milliseconds.
-/
import QCert.BianSelingerUn.LevelCalc
import QCert.Exact.Roots

namespace QCert.LevelCheck

open Matrix

/-! ### `ℤ[ω]` -/

/-- An element of `ℤ[ω]`: `a0 + a1 ω + a2 ω² + a3 ω³` with `ω⁴ = -1`. -/
structure ZW where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ

namespace ZW

def zero : ZW := ⟨0, 0, 0, 0⟩

def one : ZW := ⟨1, 0, 0, 0⟩

/-- `2`, the identity entry of a letter scaled by `2`. -/
def two : ZW := ⟨2, 0, 0, 0⟩

def add (x y : ZW) : ZW := ⟨x.a0 + y.a0, x.a1 + y.a1, x.a2 + y.a2, x.a3 + y.a3⟩

/-- Multiplication, with `ω⁴ = -1`, `ω⁵ = -ω`, `ω⁶ = -ω²`. -/
def mul (x y : ZW) : ZW :=
  ⟨x.a0 * y.a0 - (x.a1 * y.a3 + x.a2 * y.a2 + x.a3 * y.a1),
   x.a0 * y.a1 + x.a1 * y.a0 - (x.a2 * y.a3 + x.a3 * y.a2),
   x.a0 * y.a2 + x.a1 * y.a1 + x.a2 * y.a0 - x.a3 * y.a3,
   x.a0 * y.a3 + x.a1 * y.a2 + x.a2 * y.a1 + x.a3 * y.a0⟩

def smul (c : ℤ) (x : ZW) : ZW := ⟨c * x.a0, c * x.a1, c * x.a2, c * x.a3⟩

def beq (x y : ZW) : Bool :=
  decide (x.a0 = y.a0) && decide (x.a1 = y.a1) && decide (x.a2 = y.a2) && decide (x.a3 = y.a3)

/-- Into `ℚ(ω)`. -/
def toQ (x : ZW) : QOmega := ⟨x.a0, x.a1, x.a2, x.a3⟩

/-- An integer in `ℚ(ω)`. -/
def qint (c : ℤ) : QOmega := ⟨c, 0, 0, 0⟩

/-- `2 z` as an element of `ℤ[ω]` (when it is one, `int2 z`). -/
def ofQ2 (z : QOmega) : ZW :=
  ⟨(2 * z.a0).num, (2 * z.a1).num, (2 * z.a2).num, (2 * z.a3).num⟩

/-- Whether `2 z ∈ ℤ[ω]`. -/
def int2 (z : QOmega) : Bool :=
  Nat.beq (2 * z.a0).den 1 && Nat.beq (2 * z.a1).den 1 && Nat.beq (2 * z.a2).den 1 &&
    Nat.beq (2 * z.a3).den 1

theorem toQ_zero : toQ zero = 0 := by simp [toQ, zero]

theorem toQ_one : toQ one = 1 := by simp [toQ, one]

theorem qint_one : qint 1 = 1 := by simp [qint]

theorem toQ_two : toQ two = qint 2 := by simp [toQ, two, qint]

theorem toQ_add (x y : ZW) : toQ (add x y) = toQ x + toQ y := by
  simp [toQ, add]

theorem toQ_mul (x y : ZW) : toQ (mul x y) = toQ x * toQ y := by
  ext <;> simp only [toQ, mul, Quartic.mul_def] <;> push_cast <;> ring

theorem qint_mul (c : ℤ) (z : QOmega) :
    qint c * z = ⟨c * z.a0, c * z.a1, c * z.a2, c * z.a3⟩ := by
  ext <;> simp [qint]

theorem qint_mul_qint (c d : ℤ) : qint c * qint d = qint (c * d) := by
  ext <;> simp [qint]

theorem qint_pow (c : ℤ) (k : ℕ) : qint c ^ k = qint (c ^ k) := by
  induction k with
  | zero => simp [qint_one]
  | succ k ih => rw [pow_succ, ih, qint_mul_qint, pow_succ]

theorem toQ_smul (c : ℤ) (x : ZW) : toQ (smul c x) = qint c * toQ x := by
  rw [qint_mul]; simp [toQ, smul]

theorem smul_zero (c : ℤ) : smul c zero = zero := by simp [smul, zero]

theorem beq_eq {x y : ZW} (h : beq x y = true) : x = y := by
  simp only [beq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  cases x; cases y
  simp_all

theorem toQ_ofQ2 {z : QOmega} (h : int2 z = true) : toQ (ofQ2 z) = qint 2 * z := by
  simp only [int2, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  rw [qint_mul]
  simp only [toQ, ofQ2, Rat.coe_int_num_of_den_eq_one (Nat.eq_of_beq_eq_true h0),
    Rat.coe_int_num_of_den_eq_one (Nat.eq_of_beq_eq_true h1),
    Rat.coe_int_num_of_den_eq_one (Nat.eq_of_beq_eq_true h2),
    Rat.coe_int_num_of_den_eq_one (Nat.eq_of_beq_eq_true h3)]
  push_cast
  rfl

/-- Cancelling a nonzero integer factor. -/
theorem qint_mul_cancel {c : ℤ} (hc : c ≠ 0) {x y : QOmega} (h : qint c * x = qint c * y) :
    x = y := by
  rw [qint_mul, qint_mul, Quartic.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  ext
  · exact mul_left_cancel₀ hc' h0
  · exact mul_left_cancel₀ hc' h1
  · exact mul_left_cancel₀ hc' h2
  · exact mul_left_cancel₀ hc' h3

end ZW

open ZW

/-! ### Tables -/

/-- A matrix as a list of rows. -/
abbrev FM := List (List ZW)

/-- The `i`-th element of a row, `zero` beyond its end. -/
def nth : List ZW → ℕ → ZW
  | [], _ => zero
  | x :: _, 0 => x
  | _ :: l, i + 1 => nth l i

/-- The `i`-th row, `[]` beyond the end. -/
def nthRow : FM → ℕ → List ZW
  | [], _ => []
  | r :: _, 0 => r
  | _ :: A, i + 1 => nthRow A i

/-- The `m × m` table of `f`. -/
def tab (m : ℕ) (f : ℕ → ℕ → ZW) : FM :=
  (List.range m).map fun i => (List.range m).map fun j => f i j

def sumL : List ZW → ZW
  | [] => zero
  | x :: l => add x (sumL l)

/-- The entry `(i, j)` of `A * B`. -/
def dot (m : ℕ) (A B : FM) (i j : ℕ) : ZW :=
  sumL ((List.range m).map fun k => mul (nth (nthRow A i) k) (nth (nthRow B k) j))

def mulF (m : ℕ) (A B : FM) : FM := tab m (dot m A B)

def scaleF (c : ℤ) (A : FM) : FM := A.map (List.map (smul c))

/-- The identity (not scaled). -/
def idF (m : ℕ) : FM := tab m fun i j => bif Nat.beq i j then one else zero

def powF (m : ℕ) (A : FM) : ℕ → FM
  | 0 => idF m
  | k + 1 => mulF m (powF m A k) A

def beqRow : List ZW → List ZW → Bool
  | [], [] => true
  | x :: r, y :: s => beq x y && beqRow r s
  | _, _ => false

def beqM : FM → FM → Bool
  | [], [] => true
  | r :: A, s :: B => beqRow r s && beqM A B
  | _, _ => false

/-- The entries of `2 U_[a,b]`. -/
def twoEntry (a b : ℕ) (u00 u01 u10 u11 : ZW) (i j : ℕ) : ZW :=
  bif Nat.beq i a then (bif Nat.beq j a then u00 else bif Nat.beq j b then u01 else zero)
  else bif Nat.beq i b then (bif Nat.beq j a then u10 else bif Nat.beq j b then u11 else zero)
  else bif Nat.beq i j then two else zero

/-- The table of `2 U_[a,b]`. -/
def twoF (m a b : ℕ) (U : Matrix (Fin 2) (Fin 2) QOmega) : FM :=
  tab m (twoEntry a b (ofQ2 (U 0 0)) (ofQ2 (U 0 1)) (ofQ2 (U 1 0)) (ofQ2 (U 1 1)))

/-- The entries of `2 z_[a]`. -/
def oneEntry (a : ℕ) (z : ZW) (i j : ℕ) : ZW :=
  bif Nat.beq i a then (bif Nat.beq j a then z else zero)
  else bif Nat.beq i j then two else zero

/-- The table of `2 z_[a]`. -/
def oneF (m a : ℕ) (z : QOmega) : FM := tab m (oneEntry a (ofQ2 z))

/-- A table read as a matrix. -/
def toMat (m : ℕ) (A : FM) : Matrix (Fin m) (Fin m) QOmega :=
  fun i j => toQ (nth (nthRow A i) j)

/-! ### Reading tables -/

theorem nth_eq_getElem : ∀ (l : List ZW) (i : ℕ) (h : i < l.length), nth l i = l[i]
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => nth_eq_getElem l i (by simpa using h)

theorem nthRow_eq_getElem : ∀ (A : FM) (i : ℕ) (h : i < A.length), nthRow A i = A[i]
  | _ :: _, 0, _ => rfl
  | _ :: A, i + 1, h => nthRow_eq_getElem A i (by simpa using h)

theorem nth_map (h : ZW → ZW) (hz : h zero = zero) :
    ∀ (l : List ZW) (i : ℕ), nth (l.map h) i = h (nth l i)
  | [], _ => by simp [nth, hz]
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nth_map h hz l i

theorem nthRow_map (h : List ZW → List ZW) (hn : h [] = []) :
    ∀ (A : FM) (i : ℕ), nthRow (A.map h) i = h (nthRow A i)
  | [], _ => by simp [nthRow, hn]
  | _ :: _, 0 => rfl
  | _ :: A, i + 1 => nthRow_map h hn A i

theorem toMat_tab (m : ℕ) (f : ℕ → ℕ → ZW) (i j : Fin m) :
    toMat m (tab m f) i j = toQ (f i j) := by
  simp only [toMat, tab]
  rw [nthRow_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
    nth_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

theorem toQ_sumL (l : List ZW) : toQ (sumL l) = (l.map toQ).sum := by
  induction l with
  | nil => simp [sumL, toQ_zero]
  | cons x l ih => simp [sumL, toQ_add, ih]

theorem sum_map_range (g : ℕ → QOmega) (m : ℕ) :
    ((List.range m).map g).sum = ∑ k ∈ Finset.range m, g k := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem toMat_mulF (m : ℕ) (A B : FM) : toMat m (mulF m A B) = toMat m A * toMat m B := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, mulF, toMat_tab, dot, toQ_sumL, List.map_map, sum_map_range,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, toQ_mul, toMat]

theorem toMat_scaleF (m : ℕ) (c : ℤ) (A : FM) :
    toMat m (scaleF c A) = qint c • toMat m A := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat, scaleF, Matrix.smul_apply, smul_eq_mul]
  rw [nthRow_map _ rfl, nth_map _ (smul_zero c), toQ_smul]

theorem cond_beq_fin {m : ℕ} (x y : Fin m) (p q : ZW) :
    (bif Nat.beq x.val y.val then p else q) = if x = y then p else q := by
  by_cases h : x = y
  · subst h; simp
  · have : Nat.beq x.val y.val = false := by
      cases hb : Nat.beq x.val y.val
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)) h
    simp [this, h]

theorem toMat_idF (m : ℕ) : toMat m (idF m) = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [idF, toMat_tab, cond_beq_fin, Matrix.one_apply]
  split_ifs <;> simp [toQ_one, toQ_zero]

theorem toMat_powF (m : ℕ) (A : FM) (k : ℕ) : toMat m (powF m A k) = toMat m A ^ k := by
  induction k with
  | zero => rw [powF, toMat_idF, pow_zero]
  | succ k ih => rw [powF, toMat_mulF, ih, pow_succ]

theorem toMat_twoF {m : ℕ} {a b : Fin m} (hab : a ≠ b) {U : Matrix (Fin 2) (Fin 2) QOmega}
    (h00 : int2 (U 0 0) = true) (h01 : int2 (U 0 1) = true) (h10 : int2 (U 1 0) = true)
    (h11 : int2 (U 1 1) = true) : toMat m (twoF m a b U) = qint 2 • twoLevel a b U := by
  refine Matrix.ext fun i j => ?_
  rw [twoF, toMat_tab, Matrix.smul_apply, smul_eq_mul, twoLevel_apply hab, Matrix.one_apply]
  simp only [twoEntry, cond_beq_fin]
  split_ifs <;> simp [toQ_ofQ2 h00, toQ_ofQ2 h01, toQ_ofQ2 h10, toQ_ofQ2 h11, toQ_two, toQ_zero]

theorem toMat_oneF {m : ℕ} (a : Fin m) {z : QOmega} (hz : int2 z = true) :
    toMat m (oneF m a z) = qint 2 • oneLevel a z := by
  refine Matrix.ext fun i j => ?_
  rw [oneF, toMat_tab, Matrix.smul_apply, smul_eq_mul, oneLevel_apply, Matrix.one_apply]
  simp only [oneEntry, cond_beq_fin]
  by_cases hi : i = a
  · subst hi
    by_cases hj : j = i
    · subst hj; simp [toQ_ofQ2 hz]
    · simp [hj, Ne.symm hj, toQ_zero]
  · simp only [hi, if_false, false_and]
    split_ifs <;> simp [toQ_two, toQ_zero]

theorem beqRow_eq : ∀ {r s : List ZW}, beqRow r s = true → r = s
  | [], [], _ => rfl
  | x :: r, y :: s, h => by
    simp only [beqRow, Bool.and_eq_true] at h
    rw [beq_eq h.1, beqRow_eq h.2]

theorem beqM_eq : ∀ {A B : FM}, beqM A B = true → A = B
  | [], [], _ => rfl
  | r :: A, s :: B, h => by
    simp only [beqM, Bool.and_eq_true] at h
    rw [beqRow_eq h.1, beqM_eq h.2]

theorem smul_cancel {m : ℕ} {c : ℤ} (hc : c ≠ 0) {A B : Matrix (Fin m) (Fin m) QOmega}
    (h : qint c • A = qint c • B) : A = B := by
  refine Matrix.ext fun i j => ?_
  have e := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  exact qint_mul_cancel hc e

/-! ### Expressions -/

/-- Products of level matrices: the shape of the identities checked. -/
inductive MExpr (m : ℕ) where
  | two (a b : Fin m) (U : Matrix (Fin 2) (Fin 2) QOmega)
  | one (a : Fin m) (z : QOmega)
  | id
  | mul (x y : MExpr m)
  | pow (x : MExpr m) (k : ℕ)

namespace MExpr

variable {m : ℕ}

/-- The matrix. -/
noncomputable def denote : MExpr m → Matrix (Fin m) (Fin m) QOmega
  | two a b U => twoLevel a b U
  | one a z => oneLevel a z
  | id => 1
  | mul x y => denote x * denote y
  | pow x k => denote x ^ k

/-- The number of letters: the table is `2 ^ scale` times the matrix. -/
def scale : MExpr m → ℕ
  | two _ _ _ => 1
  | one _ _ => 1
  | id => 0
  | mul x y => scale x + scale y
  | pow x k => k * scale x

/-- The side conditions: distinct indices, entries in `½ ℤ[ω]`. -/
def ok : MExpr m → Bool
  | two a b U =>
    !Nat.beq a b && int2 (U 0 0) && int2 (U 0 1) && int2 (U 1 0) && int2 (U 1 1)
  | one _ z => int2 z
  | id => true
  | mul x y => ok x && ok y
  | pow x _ => ok x

/-- The table of `2 ^ scale e` times the matrix. -/
def eval : MExpr m → FM
  | two a b U => twoF m a b U
  | one a z => oneF m a z
  | id => idF m
  | mul x y => mulF m (eval x) (eval y)
  | pow x k => powF m (eval x) k

theorem toMat_eval (e : MExpr m) (h : ok e = true) :
    toMat m (eval e) = qint (2 ^ scale e) • denote e := by
  induction e with
  | two a b U =>
    simp only [ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hab, h00⟩, h01⟩, h10⟩, h11⟩ := h
    have hab' : a ≠ b := fun e => by subst e; simp at hab
    rw [eval, scale, pow_one, denote, toMat_twoF hab' h00 h01 h10 h11]
  | one a z =>
    rw [eval, scale, pow_one, denote, toMat_oneF a h]
  | id =>
    rw [eval, scale, pow_zero, denote, toMat_idF, qint_one, one_smul]
  | mul x y ihx ihy =>
    simp only [ok, Bool.and_eq_true] at h
    rw [eval, denote, scale, toMat_mulF, ihx h.1, ihy h.2, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, qint_mul_qint, ← pow_add]
  | pow x k ih =>
    rw [eval, denote, scale, toMat_powF, ih h, smul_pow, qint_pow, ← pow_mul, mul_comm]

/-- The two sides compared at a common scale. -/
def check (e₁ e₂ : MExpr m) : Bool :=
  ok e₁ && ok e₂ &&
    beqM (scaleF (2 ^ scale e₂) (eval e₁)) (scaleF (2 ^ scale e₁) (eval e₂))

/-- Soundness of the check. -/
theorem check_sound {e₁ e₂ : MExpr m} (h : check e₁ e₂ = true) :
    denote e₁ = denote e₂ := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e := congrArg (toMat m) (beqM_eq h3)
  rw [toMat_scaleF, toMat_scaleF, toMat_eval _ h1, toMat_eval _ h2, smul_smul, smul_smul,
    qint_mul_qint, qint_mul_qint, mul_comm (2 ^ scale e₂)] at e
  exact smul_cancel (by positivity) e

end MExpr

/-! ### The tactic -/

open Lean Meta Elab Tactic

/-- Reify a product of level matrices over `Fin m` into `MExpr m`. -/
partial def reify (m : Expr) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, x, y]) =>
    return mkApp3 (mkConst ``QCert.LevelCheck.MExpr.mul) m (← reify m x) (← reify m y)
  | (``HPow.hPow, #[_, _, _, _, x, k]) =>
    return mkApp3 (mkConst ``QCert.LevelCheck.MExpr.pow) m (← reify m x) k
  | (``QCert.twoLevel, #[_, _, _, a, b, U]) =>
    return mkApp4 (mkConst ``QCert.LevelCheck.MExpr.two) m a b U
  | (``QCert.oneLevel, #[_, _, _, a, z]) =>
    return mkApp3 (mkConst ``QCert.LevelCheck.MExpr.one) m a z
  | (``OfNat.ofNat, #[_, n, _]) =>
    if n.rawNatLit? == some 1 then return mkApp (mkConst ``QCert.LevelCheck.MExpr.id) m
    else throwError "level_check: unexpected numeral{indentExpr e}"
  | (``One.one, #[_, _]) => return mkApp (mkConst ``QCert.LevelCheck.MExpr.id) m
  | _ => throwError "level_check: cannot reify{indentExpr e}"

/-- Close a goal `A = B` between products of `twoLevel`, `oneLevel`, `1` over
`Matrix (Fin m) (Fin m) QOmega` by evaluating both sides on integer tables
(`MExpr.check`, decided by the kernel). -/
elab "level_check" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (ty, lhs, rhs) := t.eq? | throwError "level_check: the goal is not an equation"
  let m ← match ty.getAppFnArgs with
    | (``Matrix, #[finm, _, _]) =>
      match finm.getAppFnArgs with
      | (``Fin, #[m]) => pure m
      | _ => throwError "level_check: not a matrix over `Fin`"
    | _ => throwError "level_check: not an equation of matrices"
  let e₁ ← reify m lhs
  let e₂ ← reify m rhs
  let chk := mkApp3 (mkConst ``QCert.LevelCheck.MExpr.check) m e₁ e₂
  let hty ← mkEq chk (mkConst ``Bool.true)
  let h ← mkFreshExprSyntheticOpaqueMVar hty
  let pf := mkApp4 (mkConst ``QCert.LevelCheck.MExpr.check_sound) m e₁ e₂ h
  let pfTy ← inferType pf
  unless ← isDefEq pfTy t do
    throwError "level_check: the reification does not match the goal{indentExpr pfTy}"
  g.assign pf
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

end QCert.LevelCheck
