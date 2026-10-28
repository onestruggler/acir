/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The cubic diagonal group modulo the quadratic one

`V hA h3 n` is the diagonal group `Dg3` of the cubic fragment modulo the
diagonal group `Dg` of the quadratic fragment, a vector space over `𝔽_d`
(every element has order dividing `d`).  `kl x` is the class of `x`, and
`tau u` the class of `T` on the form `u`; a linear circuit `Y` acts on
classes by pulling forms back along its rows (`cj_atomT`).

Rules (35), (37), (38), (40), (42) of Blake (arXiv:2603.06466), with `CS`
and `CCZ` written out by Definitions 17 and 18 as products of atoms
(`csQ_dec`, `cczQ_dec`), become relations among the classes `tau u`
(`cs`, `ccz`), on any two or three forms that some linear circuit has as
rows.
-/
import QCert.PhaseAffine.CubeDiag

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ} [Fact d.Prime]

local notation "𝒢" => gateData d lv

/-! ### The quotient -/

section Quot

variable (hA : Admissible d lv) (h3 : 3 ≤ lv)

/-- The cubic diagonal group as a type. -/
@[ext]
structure D3 (_hA : Admissible d lv) (h3 : 3 ≤ lv) (n : ℕ) where
  /-- The underlying class of circuits. -/
  val : Q d lv n
  mem : val ∈ Dg3 h3 n

/-- An element of the cubic diagonal group as an element of `D3`. -/
def D3.of {hA : Admissible d lv} {h3 : 3 ≤ lv} {n : ℕ} (x : Q d lv n) (hx : x ∈ Dg3 h3 n) :
    D3 hA h3 n :=
  ⟨x, hx⟩

noncomputable instance (n : ℕ) : CommGroup (D3 hA h3 n) where
  mul a b := ⟨a.val * b.val, mul_mem a.mem b.mem⟩
  one := ⟨1, one_mem _⟩
  inv a := ⟨a.val⁻¹, inv_mem a.mem⟩
  mul_assoc a b c := D3.ext (mul_assoc a.val b.val c.val)
  one_mul a := D3.ext (one_mul a.val)
  mul_one a := D3.ext (mul_one a.val)
  inv_mul_cancel a := D3.ext (inv_mul_cancel a.val)
  mul_comm a b := D3.ext (dg3_commute hA h3 a.mem b.mem).eq

theorem D3.val_mul {n : ℕ} (x y : D3 hA h3 n) : (x * y).val = x.val * y.val := rfl

theorem D3.val_one {n : ℕ} : (1 : D3 hA h3 n).val = 1 := rfl

theorem D3.val_inv {n : ℕ} (x : D3 hA h3 n) : (x⁻¹).val = x.val⁻¹ := rfl

theorem D3.val_pow {n : ℕ} (x : D3 hA h3 n) (k : ℕ) : (x ^ k).val = x.val ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k ih => rw [pow_succ, D3.val_mul, ih, pow_succ]

theorem D3.val_mem {n : ℕ} (x : D3 hA h3 n) : x.val ∈ Dg3 h3 n := x.mem

theorem D3.val_of {n : ℕ} (x : Q d lv n) (hx : x ∈ Dg3 h3 n) :
    (D3.of (hA := hA) x hx).val = x := rfl

theorem D3.ext' {n : ℕ} {x y : D3 hA h3 n} (h : x.val = y.val) : x = y := D3.ext h

/-- The quadratic diagonal group inside `D3`. -/
def H3 (n : ℕ) : Subgroup (D3 hA h3 n) where
  carrier := {x | x.val ∈ Dg (two_le_of_three h3) n}
  mul_mem' {a b} ha hb := by
    show (a * b).val ∈ Dg (two_le_of_three h3) n
    rw [D3.val_mul]; exact mul_mem ha hb
  one_mem' := by
    show (1 : D3 hA h3 n).val ∈ Dg (two_le_of_three h3) n
    rw [D3.val_one]; exact one_mem _
  inv_mem' {a} ha := by
    show (a⁻¹).val ∈ Dg (two_le_of_three h3) n
    rw [D3.val_inv]; exact inv_mem ha

/-- The cubic diagonal group modulo the quadratic one. -/
abbrev V (n : ℕ) := Additive (D3 hA h3 n ⧸ H3 hA h3 n)

theorem V_exp (n : ℕ) : ∀ x : V hA h3 n, d • x = 0 := by
  intro x
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : x = Additive.ofMul (QuotientGroup.mk a : D3 hA h3 n ⧸ H3 hA h3 n) := by
    rw [ha]; rfl
  have : a ^ d = 1 := D3.ext' hA h3 (by
    rw [D3.val_pow, D3.val_one]; exact dg3_pow_d hA h3 (D3.val_mem hA h3 a))
  rw [hx, ← ofMul_pow, ← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  rfl

noncomputable instance (n : ℕ) : Module (ZMod d) (V hA h3 n) :=
  AddCommGroup.zmodModule (V_exp hA h3 n)

theorem V_val_smul {n : ℕ} (k : ZMod d) (x : V hA h3 n) : k.val • x = k • x := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod d), ZMod.natCast_zmod_val]

/-- The class of an element of the cubic diagonal group (`0` outside it). -/
noncomputable def kl {n : ℕ} (x : Q d lv n) : V hA h3 n := by
  classical
  exact if h : x ∈ Dg3 h3 n then Additive.ofMul (QuotientGroup.mk (D3.of x h)) else 0

variable {hA h3}

theorem kl_of {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) :
    kl hA h3 x = Additive.ofMul (QuotientGroup.mk (D3.of x hx)) := by
  classical
  simp only [kl, dif_pos hx]

theorem kl_mul {n : ℕ} {x y : Q d lv n} (hx : x ∈ Dg3 h3 n) (hy : y ∈ Dg3 h3 n) :
    kl hA h3 (x * y) = kl hA h3 x + kl hA h3 y := by
  rw [kl_of hx, kl_of hy, kl_of (mul_mem hx hy)]
  rfl

theorem kl_one {n : ℕ} : kl hA h3 (1 : Q d lv n) = 0 := by
  rw [kl_of (one_mem _)]; rfl

theorem kl_inv {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) :
    kl hA h3 x⁻¹ = -kl hA h3 x := by
  rw [eq_neg_iff_add_eq_zero, ← kl_mul (inv_mem hx) hx, inv_mul_cancel, kl_one]

theorem kl_pow {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) (k : ℕ) :
    kl hA h3 (x ^ k) = k • kl hA h3 x := by
  induction k with
  | zero => rw [pow_zero, kl_one, zero_smul]
  | succ k ih => rw [pow_succ, kl_mul (pow_mem hx k) hx, ih, succ_nsmul]

theorem kl_valpow {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) (k : ZMod d) :
    kl hA h3 (x ^ k.val) = k • kl hA h3 x := by
  rw [kl_pow hx, V_val_smul]

theorem kl_dg {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg (two_le_of_three h3) n) :
    kl hA h3 x = 0 := by
  rw [kl_of (dg_mem3 h3 hx)]
  show Additive.ofMul _ = Additive.ofMul 1
  congr 1
  exact (QuotientGroup.eq_one_iff _).2 hx

theorem mem_dg_of_cl {n : ℕ} {x : Q d lv n} (hx : x ∈ Dg3 h3 n) (h : kl hA h3 x = 0) :
    x ∈ Dg (two_le_of_three h3) n := by
  rw [kl_of hx] at h
  exact (QuotientGroup.eq_one_iff (D3.of (hA := hA) x hx)).1 (Additive.ofMul.injective h)

/-- The class of `T` on a form. -/
noncomputable def tau {n : ℕ} (u : Lab d (n + 1)) : V hA h3 (n + 1) :=
  kl hA h3 (atomL (Gate.T h3) u)

/-- The class of a conjugate by a linear circuit. -/
noncomputable def cj {n : ℕ} (Y : C d lv (n + 1)) (x : Q d lv (n + 1)) : V hA h3 (n + 1) :=
  kl hA h3 ((mk Y)⁻¹ * x * mk Y)

theorem cj_mul {n : ℕ} {Y : C d lv (n + 1)} (hY : IsLinW Y) {x y : Q d lv (n + 1)}
    (hx : x ∈ Dg3 h3 (n + 1)) (hy : y ∈ Dg3 h3 (n + 1)) :
    cj (hA := hA) (h3 := h3) Y (x * y) = cj (hA := hA) (h3 := h3) Y x + cj (hA := hA) (h3 := h3) Y y := by
  unfold cj
  rw [show (mk Y)⁻¹ * (x * y) * mk Y = ((mk Y)⁻¹ * x * mk Y) * ((mk Y)⁻¹ * y * mk Y) by group]
  exact kl_mul (conj_lin_dg3 hA h3 _ hY _ hx) (conj_lin_dg3 hA h3 _ hY _ hy)

theorem cj_inv {n : ℕ} {Y : C d lv (n + 1)} (hY : IsLinW Y) {x : Q d lv (n + 1)}
    (hx : x ∈ Dg3 h3 (n + 1)) : cj (hA := hA) (h3 := h3) Y x⁻¹ = -cj (hA := hA) (h3 := h3) Y x := by
  unfold cj
  rw [show (mk Y)⁻¹ * x⁻¹ * mk Y = ((mk Y)⁻¹ * x * mk Y)⁻¹ by group]
  exact kl_inv (conj_lin_dg3 hA h3 _ hY _ hx)

theorem cj_valpow {n : ℕ} {Y : C d lv (n + 1)} (hY : IsLinW Y) {x : Q d lv (n + 1)}
    (hx : x ∈ Dg3 h3 (n + 1)) (k : ZMod d) :
    cj (hA := hA) (h3 := h3) Y (x ^ k.val) = k • cj (hA := hA) (h3 := h3) Y x := by
  unfold cj
  rw [← conjInv_pow]
  exact kl_valpow (conj_lin_dg3 hA h3 _ hY _ hx) k

theorem cj_dg {n : ℕ} {Y : C d lv (n + 1)} (hY : IsLinW Y) {x : Q d lv (n + 1)}
    (hx : x ∈ Dg (two_le_of_three h3) (n + 1)) : cj (hA := hA) (h3 := h3) Y x = 0 :=
  kl_dg (conj_lin_dg hA _ Y hY x hx)

theorem cj_atomT {n : ℕ} {Y : C d lv (n + 1)} (hY : IsLinW Y) (u : Lab d (n + 1)) :
    cj (hA := hA) (h3 := h3) Y (atomL (Gate.T h3) u) = tau (hA := hA) (h3 := h3) (pb u Y) := by
  unfold cj tau
  rw [atomL_conj hA _ (relT1CX h3) u Y hY]

theorem cj_mul_left {n : ℕ} {Y P : C d lv (n + 1)} (x : Q d lv (n + 1)) :
    cj (hA := hA) (h3 := h3) (P * Y) x = cj (hA := hA) (h3 := h3) Y ((mk P)⁻¹ * x * mk P) := by
  unfold cj
  rw [map_mul]; congr 1; group

theorem tau_zero {n : ℕ} : tau (hA := hA) (h3 := h3) (0 : Lab d (n + 1)) = 0 := by
  unfold tau; rw [atomL_zero, kl_one]

theorem tau_smul {n : ℕ} (c : ZMod d) (u : Lab d (n + 1)) :
    tau (hA := hA) (h3 := h3) (c • u) = c ^ 3 • tau (hA := hA) (h3 := h3) u := by
  unfold tau
  have hS := atomL_S_mem (d := d) (two_le_of_three h3) u
  have hZ := atomL_Z_mem (d := d) (two_le_of_three h3) u
  have hT := atomL_T_mem3 (d := d) h3 u
  rw [atomL_T_smul hA h3, kl_mul (mul_mem (dg_mem3 h3 (pow_mem hS _))
    (dg_mem3 h3 (pow_mem hZ _))) (pow_mem hT _), kl_mul (dg_mem3 h3 (pow_mem hS _))
    (dg_mem3 h3 (pow_mem hZ _)), kl_dg (pow_mem hS _), kl_dg (pow_mem hZ _), kl_valpow hT,
    zero_add, zero_add]

theorem tau_neg {n : ℕ} (u : Lab d (n + 1)) :
    tau (hA := hA) (h3 := h3) (-u) = -tau (hA := hA) (h3 := h3) u := by
  rw [show -u = (-1 : ZMod d) • u by rw [neg_one_smul], tau_smul,
    show ((-1 : ZMod d)) ^ 3 = -1 by ring, neg_one_smul]

end Quot

end QCert.PhaseAffine
