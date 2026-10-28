/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two qudits, modulo the Paulis: the toolkit

In `Gh p g 2`, with `lo x`, `hi x` a one-qudit class on wire 0, wire 1:

* the swap exchanges the wires (`SW_hi`, `SW_lo`, from (C7), (C10),
  (C11)) and commutes with `CZ` (`SW_Cz`: it is `(CZ (H ⊗ H))³` by (T4),
  and commutes with `H ⊗ H`);
* `CZ` commutes with `S` on either wire ((C8)), and the multipliers scale
  it, `M_a CZ M_a⁻¹ = CZ^{1/a}` on either wire ((C9), (C3));
* `CX = H⁻¹ CZ H` (H on wire 0), `CX' = H⁻¹ CZ H` (H on wire 1);
* (C12) and its rescalings by `M` on wire 1: `CX^{-k} S₀ CX^k =
  S₀ S₁^{k²} CZ^k` (`CX_conj_S0`), whence `CX⁻¹ CZ CX = CZ S₁²`
  (`CX_conj_Cz`);
* the swap is three `CX`: `SW = H₁² CX CX'⁻¹ CX` (`SW_eq`).

One-qudit identities are free: one-qudit circuits are complete modulo the
Paulis (`faith_one`).
-/
import QCert.QuditClifford.Step2

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-! ### Notation -/

variable (p g) in
/-- A one-qudit class on wire 0 of two. -/
noncomputable abbrev lo : Gh p g 1 →* Gh p g 2 := padh 1 1

variable (p g) in
/-- A one-qudit class on wire 1 of two. -/
noncomputable abbrev hi : Gh p g 1 →* Gh p g 2 := ιh 1

variable (p g) in
noncomputable abbrev Cz : Gh p g 2 := CZh p g 0

variable (p g) in
noncomputable def SWh : Gh p g 2 := qh p g 2 (SWAP p)

variable (p g) in
noncomputable def CXh : Gh p g 2 := qh p g 2 CX

variable (p g) in
/-- `CX` with control on wire 0 and target on wire 1. -/
noncomputable def CXh' : Gh p g 2 := (hi p g (Hq p g))⁻¹ * Cz p g * hi p g (Hq p g)

theorem lo_hi_comm (x y : Gh p g 1) : lo p g x * hi p g y = hi p g y * lo p g x :=
  (commute_padh_ιh x y).eq

theorem eq_of_σh1 {x y : Gh p g 1} (h : σh 1 x = σh 1 y) : x = y := by
  have := faith_one (p := p) (g := g) (x * y⁻¹) (by rw [map_mul, h, ← map_mul, mul_inv_cancel, map_one])
  rwa [mul_inv_eq_one] at this

theorem qh2_rule {w v : Circ 2} (h : Rule p g 2 w v) : qh p g 2 w = qh p g 2 v := by
  have := qh_rule (g := g) 0 h
  rwa [pad_zero2, pad_zero2] at this

theorem qh2_top (c : Circ 1) : qh p g 2 (top c) = hi p g (qh p g 1 c) := rfl

theorem qh2_bot (c : Circ 1) : qh p g 2 (bot c) = lo p g (qh p g 1 c) := rfl

theorem qh2_CZ : qh p g 2 CZ = Cz p g := rfl

theorem qh_neg1_pow {n k : ℕ} : qh p g n (neg1 p ^ k) = 1 := by rw [map_pow, qh_neg1, one_pow]

/-! ### The rules on two wires -/

theorem Cz_pow_p : Cz p g ^ p = 1 := by
  have := qh2_rule (g := g) Rule.C6
  rwa [map_pow, map_one] at this

theorem SW_sq : SWh p g * SWh p g = 1 := by
  have := qh2_rule (g := g) Rule.C7
  rwa [map_pow, map_one, sq] at this

theorem SW_inv : (SWh p g)⁻¹ = SWh p g := inv_eq_of_mul_eq_one_left SW_sq

theorem SW_hiS : SWh p g * hi p g (qh p g 1 S) = lo p g (qh p g 1 S) * SWh p g := by
  have := qh2_rule (g := g) Rule.C10
  simpa [seq_def, map_mul] using this

theorem SW_hiH : SWh p g * hi p g (Hq p g) = lo p g (Hq p g) * SWh p g := by
  have := qh2_rule (g := g) Rule.C11
  simpa [seq_def, map_mul] using this

theorem Cz_hiS : Cz p g * hi p g (qh p g 1 S) = hi p g (qh p g 1 S) * Cz p g := czS1.eq

theorem Cz_hiMg : Cz p g * hi p g (Mq p g g) = hi p g (Mq p g g) * Cz p g ^ g.val := by
  have := qh2_rule (g := g) Rule.C9
  simpa [seq_def, map_mul, map_pow, Mq] using this

theorem SW_eq_T : SWh p g = (Cz p g * (hi p g (Hq p g) * lo p g (Hq p g))) ^ 3 := by
  simp only [SWh, SWAP, seq_def, par, map_mul, qh_neg1_pow, one_mul, qh2_top, qh2_bot, qh2_CZ]
  rw [pow_three]; simp only [mul_assoc]

theorem CXh_eq : CXh p g = (lo p g (Hq p g))⁻¹ * Cz p g * lo p g (Hq p g) := by
  simp only [CXh, CX, seq_def, map_mul, map_pow, qh2_bot, qh2_CZ]
  rw [← map_pow, ← Hq_inv, map_inv]; group

/-! ### The swap exchanges the wires -/

theorem SW_hi (x : Gh p g 1) : SWh p g * hi p g x * (SWh p g)⁻¹ = lo p g x := by
  refine Gh.induction_on (P := fun x => SWh p g * hi p g x * (SWh p g)⁻¹ = lo p g x) x
    (by simp) ?_
  intro y x hx
  rw [map_mul, map_mul, ← hx]
  have hy : SWh p g * hi p g (qh p g 1 (FreeMonoid.of y)) * (SWh p g)⁻¹ =
      lo p g (qh p g 1 (FreeMonoid.of y)) := by
    rcases y with c | c | _ | _ | y
    · rw [qh_gate0, map_one, map_one, mul_one, mul_inv_cancel]
    · cases c
      · rw [mul_inv_eq_iff_eq_mul]; exact SW_hiH
      · rw [mul_inv_eq_iff_eq_mul]; exact SW_hiS
    · rcases y with c | _ | _ | _ | _
      rw [qh_up, qh_gate0, map_one, map_one, map_one, mul_one, mul_inv_cancel]
  rw [← hy]; group

theorem SW_lo (x : Gh p g 1) : SWh p g * lo p g x * (SWh p g)⁻¹ = hi p g x := by
  rw [← SW_hi x, SW_inv]
  have := SW_sq (p := p) (g := g)
  calc SWh p g * (SWh p g * hi p g x * SWh p g) * SWh p g
      = (SWh p g * SWh p g) * hi p g x * (SWh p g * SWh p g) := by group
    _ = hi p g x := by rw [this]; group

theorem SW_comm_HH : Commute (SWh p g) (hi p g (Hq p g) * lo p g (Hq p g)) := by
  have h1 := SW_hi (p := p) (g := g) (Hq p g)
  have h2 := SW_lo (p := p) (g := g) (Hq p g)
  show SWh p g * (hi p g (Hq p g) * lo p g (Hq p g)) = (hi p g (Hq p g) * lo p g (Hq p g)) * SWh p g
  rw [mul_inv_eq_iff_eq_mul] at h1 h2
  calc SWh p g * (hi p g (Hq p g) * lo p g (Hq p g))
      = (SWh p g * hi p g (Hq p g)) * lo p g (Hq p g) := by group
    _ = lo p g (Hq p g) * (SWh p g * lo p g (Hq p g)) := by rw [h1]; group
    _ = lo p g (Hq p g) * hi p g (Hq p g) * SWh p g := by rw [h2]; group
    _ = _ := by rw [← lo_hi_comm]

/-- The swap commutes with `CZ`. -/
theorem SW_Cz : Commute (SWh p g) (Cz p g) := by
  set T := Cz p g * (hi p g (Hq p g) * lo p g (Hq p g))
  have hT : Commute (SWh p g) T := by rw [SW_eq_T]; exact (Commute.refl T).pow_left 3
  have hC : Cz p g = T * (hi p g (Hq p g) * lo p g (Hq p g))⁻¹ := by
    show Cz p g = Cz p g * (hi p g (Hq p g) * lo p g (Hq p g)) * (hi p g (Hq p g) * lo p g (Hq p g))⁻¹
    group
  rw [hC]
  exact hT.mul_right SW_comm_HH.inv_right

theorem conj_of_commute {G : Type*} [Group G] {a b : G} (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

theorem pow_pred_eq_inv {G : Type*} [Group G] {x : G} (hx : x ^ p = 1) : x ^ (p - 1) = x⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le, hx]

/-- `CZ` commutes with `S` on wire 0. -/
theorem Cz_comm_loS : Commute (Cz p g) (lo p g (qh p g 1 S)) := by
  have h := (czS1 (p := p) (g := g)).map (MulAut.conj (SWh p g))
  simp only [MulAut.conj_apply] at h
  rwa [conj_of_commute SW_Cz, SW_hi] at h

theorem Cz_comm_loSq (c : ZMod p) : Commute (Cz p g) (lo p g (Sq p g c)) := by
  rw [Sq, map_pow]; exact Cz_comm_loS.pow_right _

theorem Cz_comm_hiSq (c : ZMod p) : Commute (Cz p g) (hi p g (Sq p g c)) := by
  rw [Sq, map_pow]; exact czS1.pow_right _

/-! ### Powers of `CZ` and the multipliers -/

theorem Cz_val_add (a b : ZMod p) : Cz p g ^ (a + b).val = Cz p g ^ a.val * Cz p g ^ b.val :=
  pow_val_add Cz_pow_p a b

theorem Cz_val_mul (a b : ZMod p) : Cz p g ^ (a * b).val = (Cz p g ^ a.val) ^ b.val :=
  pow_val_mul Cz_pow_p a b

theorem conj_pow_inv {G : Type*} [Group G] (a b : G) (n : ℕ) :
    (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  have := conj_pow (a := a⁻¹) (b := b) (i := n)
  rwa [inv_inv] at this

theorem hi_Mq_conj {a : ZMod p} (ha : a ≠ 0) (c : ZMod p) :
    (hi p g (Mq p g a))⁻¹ * Cz p g ^ c.val * hi p g (Mq p g a) = Cz p g ^ (c * a).val := by
  obtain ⟨i, rfl⟩ := exists_log (g := g) ha
  clear ha
  rw [Mq_g_pow_nat, map_pow]
  have hg : (hi p g (Mq p g g))⁻¹ * Cz p g * hi p g (Mq p g g) = Cz p g ^ g.val := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul, Cz_hiMg]
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
    rw [pow_succ (hi p g (Mq p g g)) i, mul_inv_rev,
      show (hi p g (Mq p g g))⁻¹ * (hi p g (Mq p g g) ^ i)⁻¹ * Cz p g ^ c.val *
        (hi p g (Mq p g g) ^ i * hi p g (Mq p g g)) = (hi p g (Mq p g g))⁻¹ *
        ((hi p g (Mq p g g) ^ i)⁻¹ * Cz p g ^ c.val * hi p g (Mq p g g) ^ i) * hi p g (Mq p g g) by
        group, ih, ← conj_pow_inv, hg, ← Cz_val_mul]
    congr 2; ring

theorem lo_Mq_conj {a : ZMod p} (ha : a ≠ 0) (c : ZMod p) :
    (lo p g (Mq p g a))⁻¹ * Cz p g ^ c.val * lo p g (Mq p g a) = Cz p g ^ (c * a).val := by
  have h := congrArg (MulAut.conj (SWh p g)) (hi_Mq_conj (g := g) ha c)
  simp only [MulAut.conj_apply, map_mul, map_inv] at h
  have e : ∀ x : Gh p g 1, SWh p g * hi p g x * (SWh p g)⁻¹ = lo p g x := SW_hi
  have hz : ∀ k : ℕ, SWh p g * Cz p g ^ k * (SWh p g)⁻¹ = Cz p g ^ k := fun k =>
    conj_of_commute (SW_Cz.pow_right k)
  calc (lo p g (Mq p g a))⁻¹ * Cz p g ^ c.val * lo p g (Mq p g a)
      = (SWh p g * hi p g (Mq p g a) * (SWh p g)⁻¹)⁻¹ * (SWh p g * Cz p g ^ c.val * (SWh p g)⁻¹) *
          (SWh p g * hi p g (Mq p g a) * (SWh p g)⁻¹) := by rw [e, hz]
    _ = SWh p g * ((hi p g (Mq p g a))⁻¹ * Cz p g ^ c.val * hi p g (Mq p g a)) * (SWh p g)⁻¹ := by
        group
    _ = Cz p g ^ (c * a).val := by rw [hi_Mq_conj ha, hz]

theorem hi_Mq_conj' {a : ZMod p} (ha : a ≠ 0) (c : ZMod p) :
    hi p g (Mq p g a) * Cz p g ^ c.val * (hi p g (Mq p g a))⁻¹ = Cz p g ^ (c * a⁻¹).val := by
  rw [← inv_inv (hi p g (Mq p g a)), ← map_inv, Mq_inv ha, inv_inv]
  exact hi_Mq_conj (inv_ne_zero ha) c

theorem lo_Mq_conj' {a : ZMod p} (ha : a ≠ 0) (c : ZMod p) :
    lo p g (Mq p g a) * Cz p g ^ c.val * (lo p g (Mq p g a))⁻¹ = Cz p g ^ (c * a⁻¹).val := by
  rw [← inv_inv (lo p g (Mq p g a)), ← map_inv, Mq_inv ha, inv_inv]
  exact lo_Mq_conj (inv_ne_zero ha) c

theorem Cz_val_one : Cz p g ^ (1 : ZMod p).val = Cz p g := pow_val_one Cz_pow_p

theorem Cz_val_neg_one : Cz p g ^ (-1 : ZMod p).val = (Cz p g)⁻¹ := by
  rw [pow_val_neg Cz_pow_p, Cz_val_one]

/-! ### `CX` -/

theorem CXh_pow_p : CXh p g ^ p = 1 := by
  rw [CXh_eq, conj_pow_inv, Cz_pow_p]; group

theorem CXh_val_neg (k : ZMod p) : CXh p g ^ (-k).val = (CXh p g ^ k.val)⁻¹ := pow_val_neg CXh_pow_p k

theorem Hsq_eq_M : Hq p g ^ 2 = Mq p g (-1) := Hq_sq

/-- `H` on wire 0 conjugates `CZ` to `CX⁻¹`. -/
theorem loH_conj_Cz : lo p g (Hq p g) * Cz p g * (lo p g (Hq p g))⁻¹ = (CXh p g)⁻¹ := by
  have hn1 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have h1 : lo p g (Mq p g (-1)) * Cz p g * (lo p g (Mq p g (-1)))⁻¹ = (Cz p g)⁻¹ := by
    have := lo_Mq_conj' (g := g) hn1 1
    rwa [one_mul, Cz_val_one, inv_neg, inv_one, Cz_val_neg_one] at this
  have e : lo p g (Hq p g) = (lo p g (Hq p g))⁻¹ * lo p g (Mq p g (-1)) := by
    rw [← Hq_sq, map_pow, pow_two]; group
  rw [CXh_eq]
  conv_lhs => rw [e]
  calc (lo p g (Hq p g))⁻¹ * lo p g (Mq p g (-1)) * Cz p g * ((lo p g (Hq p g))⁻¹ *
        lo p g (Mq p g (-1)))⁻¹
      = (lo p g (Hq p g))⁻¹ * (lo p g (Mq p g (-1)) * Cz p g * (lo p g (Mq p g (-1)))⁻¹) *
          lo p g (Hq p g) := by group
    _ = _ := by rw [h1]; group

theorem lo_Mq_conj_CX {a : ZMod p} (ha : a ≠ 0) :
    lo p g (Mq p g a) * CXh p g * (lo p g (Mq p g a))⁻¹ = CXh p g ^ a.val := by
  have h1 : lo p g (Hq p g) * lo p g (Mq p g a) * (lo p g (Hq p g))⁻¹ = (lo p g (Mq p g a))⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, Hq_conj_Mq ha, map_inv]
  have e : lo p g (Mq p g a) = (lo p g (Hq p g))⁻¹ * (lo p g (Mq p g a))⁻¹ * lo p g (Hq p g) := by
    rw [← h1]; group
  rw [CXh_eq]
  conv_lhs => rw [e]
  have h2 := lo_Mq_conj (g := g) ha 1
  rw [one_mul, Cz_val_one] at h2
  calc (lo p g (Hq p g))⁻¹ * (lo p g (Mq p g a))⁻¹ * lo p g (Hq p g) *
        ((lo p g (Hq p g))⁻¹ * Cz p g * lo p g (Hq p g)) *
        ((lo p g (Hq p g))⁻¹ * (lo p g (Mq p g a))⁻¹ * lo p g (Hq p g))⁻¹
      = (lo p g (Hq p g))⁻¹ * ((lo p g (Mq p g a))⁻¹ * Cz p g * lo p g (Mq p g a)) *
          lo p g (Hq p g) := by group
    _ = _ := by rw [h2, conj_pow_inv]

theorem hi_Mq_conj_CX {a : ZMod p} (ha : a ≠ 0) :
    hi p g (Mq p g a) * CXh p g * (hi p g (Mq p g a))⁻¹ = CXh p g ^ (a⁻¹).val := by
  have hc : Commute (lo p g (Hq p g)) (hi p g (Mq p g a)) := commute_padh_ιh _ _
  have h2 := hi_Mq_conj' (g := g) ha 1
  rw [one_mul, Cz_val_one] at h2
  rw [CXh_eq]
  calc hi p g (Mq p g a) * ((lo p g (Hq p g))⁻¹ * Cz p g * lo p g (Hq p g)) * (hi p g (Mq p g a))⁻¹
      = (lo p g (Hq p g))⁻¹ * (hi p g (Mq p g a) * Cz p g * (hi p g (Mq p g a))⁻¹) *
          lo p g (Hq p g) := by
        rw [show hi p g (Mq p g a) * ((lo p g (Hq p g))⁻¹ * Cz p g * lo p g (Hq p g)) *
          (hi p g (Mq p g a))⁻¹ = hi p g (Mq p g a) * (lo p g (Hq p g))⁻¹ * Cz p g *
          (lo p g (Hq p g) * (hi p g (Mq p g a))⁻¹) by group, ← hc.inv_left.eq,
          hc.inv_right.eq]; group
    _ = _ := by rw [h2, conj_pow_inv]

theorem CX_comm_hiSq (c : ZMod p) : Commute (CXh p g) (hi p g (Sq p g c)) := by
  rw [CXh_eq]
  have h1 : Commute (lo p g (Hq p g)) (hi p g (Sq p g c)) := commute_padh_ιh _ _
  exact (h1.inv_left.mul_left (Cz_comm_hiSq c)).mul_left h1

/-! ### (C12) and its rescalings -/


theorem lo_pow_p : lo p g (qh p g 1 S) ^ p = 1 := by rw [← map_pow, S_pow_p, map_one]

theorem hi_pow_p : hi p g (qh p g 1 S) ^ p = 1 := by rw [← map_pow, S_pow_p, map_one]

/-- (C12) modulo the Paulis: `CX⁻¹ S₀ CX = S₁ S₀ CZ`. -/
theorem C12h : (CXh p g)⁻¹ * lo p g (qh p g 1 S) * CXh p g =
    hi p g (qh p g 1 S) * lo p g (qh p g 1 S) * Cz p g := by
  have h := qh2_rule (g := g) Rule.C12
  simp only [seq_def, map_mul, map_pow, qh2_bot, qh2_top, qh2_CZ] at h
  rw [show qh p g 2 CX = CXh p g from rfl, pow_pred_eq_inv lo_pow_p, pow_pred_eq_inv hi_pow_p,
    pow_pred_eq_inv CXh_pow_p] at h
  rw [← h]; group

/-! ### The diagonal classes -/

variable (p g) in
/-- `S^a` on wire 0, `S^b` on wire 1, `CZ^c`: these commute. -/
noncomputable def dgh (a b c : ZMod p) : Gh p g 2 :=
  lo p g (Sq p g a) * hi p g (Sq p g b) * Cz p g ^ c.val

theorem dgh_mul (a b c a' b' c' : ZMod p) :
    dgh p g a b c * dgh p g a' b' c' = dgh p g (a + a') (b + b') (c + c') := by
  have c1 : Commute (hi p g (Sq p g b) * Cz p g ^ c.val) (lo p g (Sq p g a')) :=
    ((commute_padh_ιh _ _).symm).mul_left ((Cz_comm_loSq a').pow_left _)
  have c2 : Commute (Cz p g ^ c.val) (hi p g (Sq p g b')) := (Cz_comm_hiSq b').pow_left _
  unfold dgh
  rw [Sq_add, Sq_add, map_mul, map_mul, Cz_val_add]
  calc lo p g (Sq p g a) * hi p g (Sq p g b) * Cz p g ^ c.val *
        (lo p g (Sq p g a') * hi p g (Sq p g b') * Cz p g ^ c'.val)
      = lo p g (Sq p g a) * ((hi p g (Sq p g b) * Cz p g ^ c.val) * lo p g (Sq p g a')) *
          hi p g (Sq p g b') * Cz p g ^ c'.val := by group
    _ = lo p g (Sq p g a) * (lo p g (Sq p g a') * hi p g (Sq p g b)) * (Cz p g ^ c.val *
          hi p g (Sq p g b')) * Cz p g ^ c'.val := by rw [c1.eq]; group
    _ = _ := by rw [c2.eq]; group

theorem dgh_zero : dgh p g 0 0 0 = 1 := by simp [dgh, Sq_zero]

theorem dgh_inv (a b c : ZMod p) : (dgh p g a b c)⁻¹ = dgh p g (-a) (-b) (-c) := by
  rw [inv_eq_iff_mul_eq_one, dgh_mul, add_neg_cancel, add_neg_cancel, add_neg_cancel, dgh_zero]

theorem dgh_pow (a b c : ZMod p) (n : ℕ) : dgh p g a b c ^ n = dgh p g (n * a) (n * b) (n * c) := by
  induction n with
  | zero => simp [dgh_zero]
  | succ n ih => rw [pow_succ, ih, dgh_mul]; congr 1 <;> push_cast <;> ring

theorem lo_Sq_dgh (a : ZMod p) : lo p g (Sq p g a) = dgh p g a 0 0 := by simp [dgh, Sq_zero]

theorem hi_Sq_dgh (b : ZMod p) : hi p g (Sq p g b) = dgh p g 0 b 0 := by simp [dgh, Sq_zero]

theorem Cz_dgh : Cz p g = dgh p g 0 0 1 := by simp [dgh, Sq_zero, Cz_val_one]

theorem Cz_pow_dgh (c : ZMod p) : Cz p g ^ c.val = dgh p g 0 0 c := by simp [dgh, Sq_zero]

theorem two_ne_zero_p (g : ZMod p) [OddGen p g] : (2 : ZMod p) ≠ 0 :=
  two_ne_zero' p (OddGen.hp2 (p := p) (g := g))

/-- (C12) rescaled by `M_{1/2}` on wire 1: `CX⁻² S₀ CX² = S₀ S₁⁴ CZ²`. -/
theorem CX2_conj_loS : (CXh p g ^ 2)⁻¹ * lo p g (qh p g 1 S) * CXh p g ^ 2 = dgh p g 1 4 2 := by
  have h2 := two_ne_zero_p (p := p) (g := g)
  have hc : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
  set m := hi p g (Mq p g 2⁻¹)
  have hCX : m * CXh p g * m⁻¹ = CXh p g ^ 2 := by
    rw [hi_Mq_conj_CX hc, inv_inv, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num,
      pow_val_natCast CXh_pow_p]
  have hlo : Commute m (lo p g (qh p g 1 S)) := (commute_padh_ιh _ _).symm
  have hS : m * hi p g (qh p g 1 S) * m⁻¹ = hi p g (Sq p g 4) := by
    rw [← map_mul, ← map_inv, ← map_mul, ← Sq_one, Mq_conj_Sq hc]
    congr 2; field_simp; norm_num
  have hZ : m * Cz p g * m⁻¹ = Cz p g ^ (2 : ZMod p).val := by
    have := hi_Mq_conj' (g := g) hc 1
    rwa [Cz_val_one, inv_inv, one_mul] at this
  calc (CXh p g ^ 2)⁻¹ * lo p g (qh p g 1 S) * CXh p g ^ 2
      = (m * CXh p g * m⁻¹)⁻¹ * lo p g (qh p g 1 S) * (m * CXh p g * m⁻¹) := by rw [hCX]
    _ = m * ((CXh p g)⁻¹ * (m⁻¹ * lo p g (qh p g 1 S) * m) * CXh p g) * m⁻¹ := by group
    _ = m * ((CXh p g)⁻¹ * lo p g (qh p g 1 S) * CXh p g) * m⁻¹ := by
        rw [show m⁻¹ * lo p g (qh p g 1 S) * m = lo p g (qh p g 1 S) by
          rw [hlo.inv_left.eq]; group]
    _ = (m * hi p g (qh p g 1 S) * m⁻¹) * (m * lo p g (qh p g 1 S) * m⁻¹) * (m * Cz p g * m⁻¹) := by
        rw [C12h]; group
    _ = _ := by
        rw [hS, conj_of_commute hlo, hZ, ← Sq_one, lo_Sq_dgh, hi_Sq_dgh, Cz_pow_dgh, dgh_mul,
          dgh_mul]
        congr 1 <;> ring

/-- `CX⁻¹ CZ CX = CZ S₁²`. -/
theorem CX_conj_Cz : (CXh p g)⁻¹ * Cz p g * CXh p g = dgh p g 0 2 1 := by
  have hC := C12h (p := p) (g := g)
  have hCz : Cz p g = (hi p g (qh p g 1 S) * lo p g (qh p g 1 S))⁻¹ *
      ((CXh p g)⁻¹ * lo p g (qh p g 1 S) * CXh p g) := by rw [hC]; group
  have hhi : (CXh p g)⁻¹ * hi p g (qh p g 1 S) * CXh p g = hi p g (qh p g 1 S) := by
    rw [← Sq_one]
    have := conj_of_commute (CX_comm_hiSq (p := p) (g := g) 1).inv_left
    rw [inv_inv] at this; exact this
  calc (CXh p g)⁻¹ * Cz p g * CXh p g
      = ((CXh p g)⁻¹ * lo p g (qh p g 1 S) * CXh p g)⁻¹ *
          ((CXh p g)⁻¹ * hi p g (qh p g 1 S) * CXh p g)⁻¹ *
          ((CXh p g * CXh p g)⁻¹ * lo p g (qh p g 1 S) * (CXh p g * CXh p g)) := by
        conv_lhs => rw [hCz]
        group
    _ = _ := by
        rw [← sq, hC, hhi, CX2_conj_loS, ← Sq_one, lo_Sq_dgh, hi_Sq_dgh, Cz_dgh, dgh_mul, dgh_mul, dgh_inv,
          dgh_inv, dgh_mul, dgh_mul]
        congr 1 <;> ring

theorem conj_eq_of_commute_inv {G : Type*} [Group G] {a b : G} (h : Commute a b) : a⁻¹ * b * a = b := by
  rw [mul_assoc, ← h.eq, inv_mul_cancel_left]

/-- `CX⁻¹ (S₀^a S₁^b CZ^c) CX = S₀^a S₁^{a + b + 2c} CZ^{a + c}`. -/
theorem CX_conj_dgh (a b c : ZMod p) :
    (CXh p g)⁻¹ * dgh p g a b c * CXh p g = dgh p g a (a + b + 2 * c) (a + c) := by
  have hlo : (CXh p g)⁻¹ * lo p g (Sq p g a) * CXh p g = dgh p g a a a := by
    rw [Sq, map_pow, ← conj_pow_inv, C12h, ← Sq_one, lo_Sq_dgh, hi_Sq_dgh,
      Cz_dgh, dgh_mul, dgh_mul, dgh_pow]
    congr 1 <;> simp [val_cast]
  have hhi : (CXh p g)⁻¹ * hi p g (Sq p g b) * CXh p g = hi p g (Sq p g b) :=
    conj_eq_of_commute_inv (CX_comm_hiSq b)
  have hz : (CXh p g)⁻¹ * Cz p g ^ c.val * CXh p g = dgh p g 0 (2 * c) c := by
    rw [← conj_pow_inv, CX_conj_Cz, dgh_pow]
    congr 1 <;> simp [val_cast] <;> ring
  calc (CXh p g)⁻¹ * dgh p g a b c * CXh p g
      = ((CXh p g)⁻¹ * lo p g (Sq p g a) * CXh p g) * ((CXh p g)⁻¹ * hi p g (Sq p g b) * CXh p g) *
          ((CXh p g)⁻¹ * Cz p g ^ c.val * CXh p g) := by unfold dgh; group
    _ = _ := by
        rw [hlo, hhi, hz, hi_Sq_dgh, dgh_mul, dgh_mul]
        congr 1 <;> ring

/-- Conjugation by `CX^n`. -/
theorem CX_pow_conj_dgh (n : ℕ) (a b c : ZMod p) :
    (CXh p g ^ n)⁻¹ * dgh p g a b c * CXh p g ^ n =
      dgh p g a (b + a * n ^ 2 + 2 * c * n) (c + a * n) := by
  induction n generalizing b c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show (CXh p g ^ n * CXh p g)⁻¹ * dgh p g a b c * (CXh p g ^ n * CXh p g) =
      (CXh p g)⁻¹ * ((CXh p g ^ n)⁻¹ * dgh p g a b c * CXh p g ^ n) * CXh p g by group, ih,
      CX_conj_dgh]
    congr 1 <;> push_cast <;> ring

theorem CX_val_conj_dgh (k a b c : ZMod p) :
    (CXh p g ^ k.val)⁻¹ * dgh p g a b c * CXh p g ^ k.val =
      dgh p g a (b + a * k ^ 2 + 2 * c * k) (c + a * k) := by
  rw [CX_pow_conj_dgh, val_cast]

/-! ### The other `CX` -/

theorem SW_Cz_conj : SWh p g * Cz p g * (SWh p g)⁻¹ = Cz p g := conj_of_commute SW_Cz

theorem SW_CX : SWh p g * CXh p g * (SWh p g)⁻¹ = CXh' p g := by
  rw [CXh_eq, CXh']
  calc SWh p g * ((lo p g (Hq p g))⁻¹ * Cz p g * lo p g (Hq p g)) * (SWh p g)⁻¹
      = (SWh p g * lo p g (Hq p g) * (SWh p g)⁻¹)⁻¹ * (SWh p g * Cz p g * (SWh p g)⁻¹) *
          (SWh p g * lo p g (Hq p g) * (SWh p g)⁻¹) := by group
    _ = _ := by rw [SW_lo, SW_Cz_conj]

theorem SW_dgh (a b c : ZMod p) : SWh p g * dgh p g a b c * (SWh p g)⁻¹ = dgh p g b a c := by
  have e : SWh p g * dgh p g a b c * (SWh p g)⁻¹ =
      (SWh p g * lo p g (Sq p g a) * (SWh p g)⁻¹) * (SWh p g * hi p g (Sq p g b) * (SWh p g)⁻¹) *
        (SWh p g * Cz p g * (SWh p g)⁻¹) ^ c.val := by
    rw [conj_pow]; unfold dgh; group
  rw [e, SW_lo, SW_hi, SW_Cz_conj, hi_Sq_dgh, lo_Sq_dgh, Cz_pow_dgh, dgh_mul, dgh_mul]
  congr 1 <;> ring

theorem CX'_val_conj_dgh (k a b c : ZMod p) :
    (CXh' p g ^ k.val)⁻¹ * dgh p g a b c * CXh' p g ^ k.val =
      dgh p g (a + b * k ^ 2 + 2 * c * k) b (c + b * k) := by
  have h := CX_val_conj_dgh (p := p) (g := g) k b a c
  have e1 : CXh' p g ^ k.val = SWh p g * CXh p g ^ k.val * (SWh p g)⁻¹ := by
    rw [← conj_pow, SW_CX]
  rw [e1, ← SW_dgh b a c]
  calc (SWh p g * CXh p g ^ k.val * (SWh p g)⁻¹)⁻¹ * (SWh p g * dgh p g b a c * (SWh p g)⁻¹) *
        (SWh p g * CXh p g ^ k.val * (SWh p g)⁻¹)
      = SWh p g * ((CXh p g ^ k.val)⁻¹ * dgh p g b a c * CXh p g ^ k.val) * (SWh p g)⁻¹ := by group
    _ = _ := by rw [h, SW_dgh]

theorem CXh'_mem_J : CXh' p g ∈ J p g 1 := by
  rw [CXh']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (ιh_mem_J _)) (CZh_mem_J 0))
    (ιh_mem_J _)

theorem dgh_mem_J (a b c : ZMod p) : dgh p g a b c ∈ J p g 1 := by
  unfold dgh
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (ιh_mem_J _)) (Subgroup.pow_mem _ (CZh_mem_J 0) _)
  rw [Sq, map_pow]
  exact Subgroup.pow_mem _ (S0h_mem_J 1) _

/-! ### The swap is three `CX` -/

theorem hiH2_conj_Cz : hi p g (Hq p g ^ 2) * Cz p g * (hi p g (Hq p g ^ 2))⁻¹ = (Cz p g)⁻¹ := by
  have hn1 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have := hi_Mq_conj' (g := g) hn1 1
  rwa [one_mul, Cz_val_one, inv_neg, inv_one, Cz_val_neg_one, ← Hq_sq] at this

theorem loH2_conj_Cz : lo p g (Hq p g ^ 2) * Cz p g * (lo p g (Hq p g ^ 2))⁻¹ = (Cz p g)⁻¹ := by
  have hn1 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have := lo_Mq_conj' (g := g) hn1 1
  rwa [one_mul, Cz_val_one, inv_neg, inv_one, Cz_val_neg_one, ← Hq_sq] at this

/-- `SWAP = H₁² CX CX'⁻¹ CX`: the derivation runs from the right-hand side to
`(CZ (H ⊗ H))³` (T4), using `H₁² CZ H₁⁻² = CZ⁻¹`, that `(H ⊗ H)²` commutes with
`CZ` and `(H ⊗ H)⁴ = 1`, and that the swap exchanges the two `H`. -/
theorem SW_eq : SWh p g = hi p g (Hq p g ^ 2) * CXh p g * (CXh' p g)⁻¹ * CXh p g := by
  set a := lo p g (Hq p g)
  set b := hi p g (Hq p g)
  set C := Cz p g
  have hab : a * b = b * a := lo_hi_comm _ _
  have hab' : b⁻¹ * a⁻¹ = (b * a)⁻¹ := by rw [← hab, mul_inv_rev]
  have hb2 : b ^ 2 * C * (b ^ 2)⁻¹ = C⁻¹ := by rw [← map_pow]; exact hiH2_conj_Cz
  have ha2 : a ^ 2 * C * (a ^ 2)⁻¹ = C⁻¹ := by rw [← map_pow]; exact loH2_conj_Cz
  have ha4 : a ^ 4 = 1 := by rw [← map_pow, Hq_pow_four, map_one]
  have hb4 : b ^ 4 = 1 := by rw [← map_pow, Hq_pow_four, map_one]
  have hHH4 : (b * a) ^ 4 = 1 := by
    rw [(show Commute b a from hab.symm).mul_pow 4, ha4, hb4, one_mul]
  have hinv : (b * a)⁻¹ = (b * a) * (b * a) ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← hHH4]; group
  have hN : (b * a) ^ 2 * C = C * (b * a) ^ 2 := by
    rw [(show Commute b a from hab.symm).mul_pow 2]
    calc b ^ 2 * a ^ 2 * C = b ^ 2 * (a ^ 2 * C * (a ^ 2)⁻¹) * a ^ 2 := by group
      _ = (b ^ 2 * C * (b ^ 2)⁻¹)⁻¹ * (b ^ 2 * a ^ 2) := by rw [ha2]; group
      _ = C * (b ^ 2 * a ^ 2) := by rw [hb2, inv_inv]
  have hSWa2 : SWh p g * a ^ 2 = b ^ 2 * SWh p g := by
    rw [← mul_inv_eq_iff_eq_mul, ← map_pow, ← map_pow]; exact SW_lo _
  have hSWb : SWh p g * b = a * SWh p g := SW_hiH
  have hSW : SWh p g = (C * (b * a)) ^ 3 := SW_eq_T
  rw [CXh_eq, CXh', map_pow]
  symm
  calc b ^ 2 * (a⁻¹ * C * a) * (b⁻¹ * C * b)⁻¹ * (a⁻¹ * C * a)
      = b ^ 2 * a⁻¹ * C * a * b⁻¹ * C⁻¹ * b * a⁻¹ * C * a := by group
    _ = b ^ 2 * a⁻¹ * C * a * b⁻¹ * (b ^ 2 * C * (b ^ 2)⁻¹) * b * a⁻¹ * C * a := by rw [hb2]
    _ = b ^ 2 * a⁻¹ * C * (a * b) * C * (b⁻¹ * a⁻¹) * C * a := by group
    _ = b ^ 2 * a⁻¹ * C * (b * a) * C * ((b * a) * (b * a) ^ 2) * C * a := by rw [hab, hab', hinv]
    _ = b ^ 2 * a⁻¹ * (C * (b * a)) * (C * (b * a)) * ((b * a) ^ 2 * C) * a := by
        simp only [mul_assoc]
    _ = b ^ 2 * a⁻¹ * (C * (b * a)) ^ 3 * (b * a) * a := by
        rw [hN, pow_three (C * (b * a)), sq (b * a)]; simp only [mul_assoc]
    _ = b ^ 2 * a⁻¹ * (SWh p g * b) * a ^ 2 := by
        rw [← hSW, sq a]; simp only [mul_assoc]
    _ = b ^ 2 * (SWh p g * a ^ 2) := by rw [hSWb]; group
    _ = b ^ 4 * SWh p g := by rw [hSWa2]; group
    _ = SWh p g := by rw [hb4, one_mul]

end QCert.QuditClifford
