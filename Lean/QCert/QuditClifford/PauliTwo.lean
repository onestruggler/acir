/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two qudits, modulo the scalars: `CZ` and the Paulis

Proposition 4.8 on two wires, in the group `Gs p g 2` of two-wire circuits
modulo the rules and the scalars: `CZ` commutes with `Z` on either wire,
and conjugates `X` on one wire to `X` there times `Z` on the other.

The route (each identity checked on the matrices for `p = 3, 5, 7` first):

* `H²` on wire 1 inverts `CZ` ((C2), (C3), (C9)); the swap ((T4), (C7),
  (C10), (C11)) moves this, and (C8), to wire 0;
* hence `CZ` commutes with `Z = H² S H² S⁻¹` on either wire, and
  `CX = H₀⁻¹ CZ H₀` commutes with `X` on wire 0 (its target);
* (C12), `CX⁻¹ S₀ CX = S₁ S₀ CZ`, conjugated by `H²` on wire 1, gives
  `CX S₀ CX⁻¹`, and with it, `H²` on wire 0 inverting `CX`,
  `CX⁻¹ Z₀ CX = Z₁ Z₀`;
* (C12) once more: `CZ X₀ CZ⁻¹ = X₀ Z₁`; the swap gives `CZ X₁ CZ⁻¹ = X₁ Z₀`.

The group-theoretic steps are lemmas in an arbitrary group (section
`TwoAlg`).
-/
import QCert.QuditClifford.PauliOne

namespace QCert.QuditClifford

/-! ### The derivations, in any group -/

section TwoAlg

variable {G : Type*} [Group G]

theorem alg_comm_Z {c A s : G} (hcA : A * c * A⁻¹ = c⁻¹) (hcs : Commute c s) :
    Commute c (A * s * A * s⁻¹) := by
  have e1 : c * A = A * c⁻¹ := by
    have : A * c⁻¹ * A⁻¹ = c := by
      rw [show A * c⁻¹ * A⁻¹ = (A * c * A⁻¹)⁻¹ by gnorm, hcA, inv_inv]
    calc c * A = (A * c⁻¹ * A⁻¹) * A := by rw [this]
      _ = A * c⁻¹ := by gnorm
  have e2 : c⁻¹ * A = A * c := by rw [← hcA]; gnorm
  show c * (A * s * A * s⁻¹) = (A * s * A * s⁻¹) * c
  calc c * (A * s * A * s⁻¹) = (c * A) * s * A * s⁻¹ := by gnorm
    _ = A * (c⁻¹ * s) * A * s⁻¹ := by rw [e1]; gnorm
    _ = A * (s * c⁻¹) * A * s⁻¹ := by rw [hcs.inv_left.eq]
    _ = A * s * (c⁻¹ * A) * s⁻¹ := by gnorm
    _ = A * s * A * (c * s⁻¹) := by rw [e2]; gnorm
    _ = A * s * A * (s⁻¹ * c) := by rw [hcs.inv_right.eq]
    _ = (A * s * A * s⁻¹) * c := by gnorm

theorem alg_conj_comm {L c Z : G} (h : Commute c Z) :
    Commute (L⁻¹ * c * L) (L⁻¹ * Z * L) := by
  show (L⁻¹ * c * L) * (L⁻¹ * Z * L) = (L⁻¹ * Z * L) * (L⁻¹ * c * L)
  calc (L⁻¹ * c * L) * (L⁻¹ * Z * L) = L⁻¹ * (c * Z) * L := by gnorm
    _ = L⁻¹ * (Z * c) * L := by rw [h.eq]
    _ = _ := by gnorm

theorem alg_conj_through {A L c d : G} (hAL : Commute A L) (h : A * c * A⁻¹ = d) :
    A * (L⁻¹ * c * L) * A⁻¹ = L⁻¹ * d * L := by
  calc A * (L⁻¹ * c * L) * A⁻¹ = (A * L⁻¹) * c * (L * A⁻¹) := by gnorm
    _ = (L⁻¹ * A) * c * (A⁻¹ * L) := by rw [hAL.inv_right.eq, hAL.inv_left.eq]
    _ = L⁻¹ * (A * c * A⁻¹) * L := by gnorm
    _ = L⁻¹ * d * L := by rw [h]

theorem alg_cx_conj {A cx s t c d : G} (h12 : cx⁻¹ * s * cx = t * s * c)
    (hA : A * cx * A⁻¹ = cx⁻¹) (hAs : Commute A s) (ht : A * t * A⁻¹ = d)
    (hc : A * c * A⁻¹ = c⁻¹) : cx * s * cx⁻¹ = d * s * c⁻¹ := by
  have hA' : A * cx⁻¹ * A⁻¹ = cx := by
    rw [show A * cx⁻¹ * A⁻¹ = (A * cx * A⁻¹)⁻¹ by gnorm, hA, inv_inv]
  have hs : A * s * A⁻¹ = s := by rw [hAs.eq]; gnorm
  calc cx * s * cx⁻¹ = (A * cx⁻¹ * A⁻¹) * (A * s * A⁻¹) * (A * cx⁻¹ * A⁻¹)⁻¹ := by rw [hA', hs]
    _ = A * (cx⁻¹ * s * cx) * A⁻¹ := by gnorm
    _ = A * (t * s * c) * A⁻¹ := by rw [h12]
    _ = (A * t * A⁻¹) * (A * s * A⁻¹) * (A * c * A⁻¹) := by gnorm
    _ = d * s * c⁻¹ := by rw [ht, hs, hc]

theorem alg_cx_Z {B cx s t c zt zb : G} (hB2 : B * B = 1) (hBcx : B * cx * B⁻¹ = cx⁻¹)
    (hcx : cx * s * cx⁻¹ = zt * t * s * c⁻¹) (h12 : cx⁻¹ * s * cx = t * s * c)
    (hBt : B * (zt * t) * B⁻¹ = zt * t) (hBs : B * s * B⁻¹ = zb * s) (hBc : B * c * B⁻¹ = c⁻¹)
    (htzb : Commute t zb) (hzb : zb = B * s * B * s⁻¹) : cx⁻¹ * zb * cx = zt * zb := by
  have hBi : B⁻¹ = B := inv_eq_of_mul_eq_one_left hB2
  have hBB : ∀ y, B * (B * y) = y := fun y => by rw [← mul_assoc, hB2, one_mul]
  have hcxB : B * cx⁻¹ * B⁻¹ = cx := by
    rw [show B * cx⁻¹ * B⁻¹ = (B * cx * B⁻¹)⁻¹ by gnorm, hBcx, inv_inv]
  calc cx⁻¹ * zb * cx = cx⁻¹ * (B * s * B * s⁻¹) * cx := by rw [hzb]
    _ = (B * cx * B⁻¹) * (B * s * B) * (B * cx⁻¹ * B⁻¹) * (cx⁻¹ * s⁻¹ * cx) := by
        rw [hBcx, hcxB]; gnorm
    _ = B * (cx * s * cx⁻¹) * B⁻¹ * (cx⁻¹ * s * cx)⁻¹ := by
        simp only [one_mul, mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left, inv_mul_cancel_left,
          mul_inv_cancel, inv_mul_cancel, mul_one, inv_one, hBi, hBB, hB2]
    _ = (B * (zt * t) * B⁻¹) * (B * s * B⁻¹) * (B * c * B⁻¹)⁻¹ * (t * s * c)⁻¹ := by
        rw [hcx, h12]; gnorm
    _ = (zt * t) * (zb * s) * (c⁻¹)⁻¹ * (t * s * c)⁻¹ := by rw [hBt, hBs, hBc]
    _ = zt * (t * zb) * t⁻¹ := by gnorm
    _ = zt * zb := by rw [htzb.eq]; gnorm

theorem alg_cz_X {c cx s t X zt zb : G} (h12 : s⁻¹ * t⁻¹ * cx⁻¹ * s * cx = c)
    (hcxX : Commute cx X) (hsX : s * X * s⁻¹ = X * zb) (hsX' : s⁻¹ * X * s = X * zb⁻¹)
    (hcxz : cx⁻¹ * zb * cx = zt * zb) (htX : Commute t X) (htzt : Commute t zt)
    (htzb : Commute t zb) (hszt : Commute s zt) (hszb : Commute s zb) (hztzb : Commute zt zb) :
    c * X * c⁻¹ = X * zt := by
  have hcxX1 : cx * X * cx⁻¹ = X := by rw [hcxX.eq]; gnorm
  have hcxX2 : cx⁻¹ * X * cx = X := conj_eq_of_commute_inv hcxX
  calc c * X * c⁻¹ = (s⁻¹ * t⁻¹) * (cx⁻¹ * (s * (cx * X * cx⁻¹) * s⁻¹) * cx) * (t * s) := by
        rw [← h12]; gnorm
    _ = (s⁻¹ * t⁻¹) * (cx⁻¹ * (s * X * s⁻¹) * cx) * (t * s) := by rw [hcxX1]
    _ = (s⁻¹ * t⁻¹) * (cx⁻¹ * (X * zb) * cx) * (t * s) := by rw [hsX]
    _ = (s⁻¹ * t⁻¹) * ((cx⁻¹ * X * cx) * (cx⁻¹ * zb * cx)) * (t * s) := by gnorm
    _ = (s⁻¹ * t⁻¹) * (X * (zt * zb)) * (t * s) := by rw [hcxX2, hcxz]
    _ = s⁻¹ * (t⁻¹ * X * t) * (t⁻¹ * zt * t) * (t⁻¹ * zb * t) * s := by gnorm
    _ = s⁻¹ * X * zt * zb * s := by
        rw [conj_eq_of_commute_inv htX, conj_eq_of_commute_inv htzt, conj_eq_of_commute_inv htzb]
    _ = (s⁻¹ * X * s) * (s⁻¹ * zt * s) * (s⁻¹ * zb * s) := by gnorm
    _ = (X * zb⁻¹) * zt * zb := by
        rw [hsX', conj_eq_of_commute_inv hszt, conj_eq_of_commute_inv hszb]
    _ = X * (zb⁻¹ * zt * zb) := by gnorm
    _ = X * zt := by rw [conj_eq_of_commute_inv hztzb.symm]

end TwoAlg

/-! ### Two wires modulo the scalars -/

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

local notation "𝐇" => qs p g 1 H
local notation "𝐒" => qs p g 1 S
local notation "𝐗" => qs p g 1 (X p)
local notation "𝐙" => qs p g 1 (Z p)

variable (p g) in
/-- One-wire classes on wire 0 of two. -/
noncomputable abbrev los : Gs p g 1 →* Gs p g 2 := pads p g 1 1

variable (p g) in
/-- One-wire classes on wire 1 of two. -/
noncomputable abbrev his : Gs p g 1 →* Gs p g 2 := ιs p g 1

local notation "𝐂" => qs p g 2 CZ
local notation "𝐖" => qs p g 2 (SWAP p)
local notation "𝐂𝐗" => qs p g 2 CX

theorem qs2_top (c : Circ 1) : qs p g 2 (top c) = his p g (qs p g 1 c) := rfl

theorem qs2_bot (c : Circ 1) : qs p g 2 (bot c) = los p g (qs p g 1 c) := rfl

theorem qs_rule2 {w v : Circ 2} (h : Rule p g 2 w v) : qs p g 2 w = qs p g 2 v := by
  have := qs_rule (g := g) 0 h
  rwa [pad_zero2, pad_zero2] at this

theorem lohi_comm (a b : Gs p g 1) : Commute (los p g a) (his p g b) := commute_pads_ιs a b

theorem qsH_inv : 𝐇⁻¹ = 𝐇 ^ 3 := by
  rw [h4_inv qsH_pow_four]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]

/-! ### The rules on two wires -/

theorem qsC_pow_p : 𝐂 ^ p = 1 := by
  rw [← map_pow, qs_rule2 Rule.C6, map_one]

theorem qsW_sq : 𝐖 * 𝐖 = 1 := by
  have := qs_rule2 (g := g) Rule.C7
  rwa [map_pow, map_one, sq] at this

theorem qsW_inv : 𝐖⁻¹ = 𝐖 := inv_eq_of_mul_eq_one_left qsW_sq

theorem qsW_hiS : 𝐖 * his p g 𝐒 = los p g 𝐒 * 𝐖 := by
  have := qs_rule2 (g := g) Rule.C10
  simpa only [seq_def, map_mul, qs2_top, qs2_bot] using this

theorem qsW_hiH : 𝐖 * his p g 𝐇 = los p g 𝐇 * 𝐖 := by
  have := qs_rule2 (g := g) Rule.C11
  simpa only [seq_def, map_mul, qs2_top, qs2_bot] using this

theorem qsC_hiS : Commute 𝐂 (his p g 𝐒) := by
  have := qs_rule2 (g := g) Rule.C8
  simp only [seq_def, map_mul, qs2_top] at this
  exact this

theorem qsC_hiM : 𝐂 * his p g (qs p g 1 (M p g)) = his p g (qs p g 1 (M p g)) * 𝐂 ^ g.val := by
  have := qs_rule2 (g := g) Rule.C9
  simp only [seq_def, map_mul, map_pow, qs2_top] at this
  exact this

theorem qsW_eq : 𝐖 = (𝐂 * (his p g 𝐇 * los p g 𝐇)) ^ 3 := by
  simp only [SWAP, seq_def, par, map_mul, map_pow, qs_neg1, one_pow, one_mul, qs2_top, qs2_bot]
  rw [pow_three]; simp only [mul_assoc]

theorem qsCX_eq : 𝐂𝐗 = (los p g 𝐇)⁻¹ * 𝐂 * los p g 𝐇 := by
  simp only [CX, seq_def, map_mul, map_pow, qs2_bot]
  rw [show los p g 𝐇 ^ 3 = (los p g 𝐇)⁻¹ by rw [← map_pow, ← qsH_inv, map_inv]]
  simp only [mul_assoc]

theorem qsCX_pow_p : 𝐂𝐗 ^ p = 1 := by
  rw [qsCX_eq, conj_pow_inv, qsC_pow_p, mul_one, inv_mul_cancel]

theorem qs_C12 : (los p g 𝐒)⁻¹ * (his p g 𝐒)⁻¹ * 𝐂𝐗⁻¹ * los p g 𝐒 * 𝐂𝐗 = 𝐂 := by
  have h := qs_rule2 (g := g) Rule.C12
  simp only [seq_def, map_mul, map_pow, qs2_top, qs2_bot] at h
  have hlo : los p g 𝐒 ^ p = 1 := by rw [← map_pow, qsS_pow_p, map_one]
  have hhi : his p g 𝐒 ^ p = 1 := by rw [← map_pow, qsS_pow_p, map_one]
  rw [pow_pred_eq_inv hlo, pow_pred_eq_inv hhi, pow_pred_eq_inv qsCX_pow_p] at h
  rw [← h]; simp only [mul_assoc]

/-! ### The swap exchanges the wires -/

theorem qsW_hi (y : Gs p g 1) : 𝐖 * his p g y * 𝐖⁻¹ = los p g y := by
  refine Gs.induction_on (P := fun y => 𝐖 * his p g y * 𝐖⁻¹ = los p g y) y (by simp) ?_
  intro y x hx
  rw [map_mul, map_mul, ← hx]
  have hy : 𝐖 * his p g (qs p g 1 (FreeMonoid.of y)) * 𝐖⁻¹ = los p g (qs p g 1 (FreeMonoid.of y)) := by
    rcases y with c | c | _ | _ | y
    · rw [qs_gate0, map_one, map_one, mul_one, mul_inv_cancel]
    · cases c
      · rw [mul_inv_eq_iff_eq_mul]; exact qsW_hiH
      · rw [mul_inv_eq_iff_eq_mul]; exact qsW_hiS
    · rcases y with c | _ | _ | _ | _
      rw [qs_up, qs_gate0, map_one, map_one, map_one, mul_one, mul_inv_cancel]
  rw [← hy]; gnorm

theorem qsW_lo (y : Gs p g 1) : 𝐖 * los p g y * 𝐖⁻¹ = his p g y := by
  rw [← qsW_hi y, qsW_inv]
  calc 𝐖 * (𝐖 * his p g y * 𝐖) * 𝐖 = (𝐖 * 𝐖) * his p g y * (𝐖 * 𝐖) := by gnorm
    _ = his p g y := by rw [qsW_sq]; gnorm

theorem qsW_C : 𝐖 * 𝐂 * 𝐖⁻¹ = 𝐂 := by
  set T := 𝐂 * (his p g 𝐇 * los p g 𝐇)
  have hT : Commute 𝐖 T := by rw [qsW_eq]; exact (Commute.refl T).pow_left 3
  have hHH : Commute 𝐖 (his p g 𝐇 * los p g 𝐇) := by
    show 𝐖 * (his p g 𝐇 * los p g 𝐇) = (his p g 𝐇 * los p g 𝐇) * 𝐖
    have h1 := qsW_hi (p := p) (g := g) 𝐇
    have h2 := qsW_lo (p := p) (g := g) 𝐇
    rw [mul_inv_eq_iff_eq_mul] at h1 h2
    calc 𝐖 * (his p g 𝐇 * los p g 𝐇) = (𝐖 * his p g 𝐇) * los p g 𝐇 := by gnorm
      _ = los p g 𝐇 * (𝐖 * los p g 𝐇) := by rw [h1]; gnorm
      _ = los p g 𝐇 * (his p g 𝐇 * 𝐖) := by rw [h2]
      _ = (his p g 𝐇 * los p g 𝐇) * 𝐖 := by rw [← mul_assoc, (lohi_comm 𝐇 𝐇).eq]
  have hC : 𝐂 = T * (his p g 𝐇 * los p g 𝐇)⁻¹ := by
    show 𝐂 = 𝐂 * (his p g 𝐇 * los p g 𝐇) * (his p g 𝐇 * los p g 𝐇)⁻¹
    rw [mul_inv_cancel_right]
  rw [conj_of_commute (by rw [hC]; exact hT.mul_right hHH.inv_right)]

/-! ### `H²` inverts `CZ` -/

theorem qs_H2_eq_Mpow : 𝐇 ^ 2 = qs p g 1 (M p g) ^ ((p - 1) / 2) := by
  have h2 := qs_rule1 (g := g) Rule.C2
  simp only [seq_def, map_mul, map_pow, qs_neg1, one_pow, one_mul] at h2
  have h3 := qs_rule1 (g := g) (Rule.C3 (((p - 1) / 2 : ℕ) : ZMod p))
  have hlt : (p - 1) / 2 < p := by have := hp.out.pos; omega
  rw [map_pow, ZMod.val_natCast, Nat.mod_eq_of_lt hlt,
    pow_half_eq_neg_one p (OddGen.hp2 g) g OddGen.hg] at h3
  rw [h2, ← h3]

theorem qsC_pow_hiM (e : ℕ) :
    𝐂 ^ e * his p g (qs p g 1 (M p g)) = his p g (qs p g 1 (M p g)) * 𝐂 ^ (e * g.val) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, mul_assoc, qsC_hiM, ← mul_assoc, ih, mul_assoc, ← pow_add, add_mul, one_mul]

theorem qsC_hiMpow (k : ℕ) :
    𝐂 * his p g (qs p g 1 (M p g)) ^ k = his p g (qs p g 1 (M p g)) ^ k * 𝐂 ^ (g.val ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, qsC_pow_hiM, ← mul_assoc, pow_succ (g.val)]

theorem qsC_pow_half : 𝐂 ^ (g.val ^ ((p - 1) / 2)) = 𝐂⁻¹ := by
  rw [← pow_val_natCast qsC_pow_p, Nat.cast_pow, ZMod.natCast_zmod_val,
    pow_half_eq_neg_one p (OddGen.hp2 g) g OddGen.hg, pow_val_neg qsC_pow_p, pow_val_one qsC_pow_p]

theorem qsC_hiH2 : 𝐂 * his p g (𝐇 ^ 2) = his p g (𝐇 ^ 2) * 𝐂⁻¹ := by
  rw [qs_H2_eq_Mpow, map_pow, qsC_hiMpow, qsC_pow_half]

theorem qs_hiH2_inv : (his p g (𝐇 ^ 2))⁻¹ = his p g (𝐇 ^ 2) := by
  rw [← map_inv, h4_sq_inv qsH_pow_four]

theorem qs_loH2_inv : (los p g (𝐇 ^ 2))⁻¹ = los p g (𝐇 ^ 2) := by
  rw [← map_inv, h4_sq_inv qsH_pow_four]

theorem qs_H4 : 𝐇 ^ 2 * 𝐇 ^ 2 = 1 := by rw [← pow_add]; exact qsH_pow_four

theorem qs_hiH2_C : his p g (𝐇 ^ 2) * 𝐂 * (his p g (𝐇 ^ 2))⁻¹ = 𝐂⁻¹ := by
  have hAA : his p g (𝐇 ^ 2) * his p g (𝐇 ^ 2) = 1 := by rw [← map_mul, qs_H4, map_one]
  rw [qs_hiH2_inv, mul_assoc, qsC_hiH2, ← mul_assoc, hAA, one_mul]

theorem qs_loH2_C : los p g (𝐇 ^ 2) * 𝐂 * (los p g (𝐇 ^ 2))⁻¹ = 𝐂⁻¹ := by
  calc los p g (𝐇 ^ 2) * 𝐂 * (los p g (𝐇 ^ 2))⁻¹
      = (𝐖 * his p g (𝐇 ^ 2) * 𝐖⁻¹) * (𝐖 * 𝐂 * 𝐖⁻¹) * (𝐖 * his p g (𝐇 ^ 2) * 𝐖⁻¹)⁻¹ := by
        rw [qsW_hi, qsW_C]
    _ = 𝐖 * (his p g (𝐇 ^ 2) * 𝐂 * (his p g (𝐇 ^ 2))⁻¹) * 𝐖⁻¹ := by gnorm
    _ = (𝐖 * 𝐂 * 𝐖⁻¹)⁻¹ := by rw [qs_hiH2_C]; gnorm
    _ = 𝐂⁻¹ := by rw [qsW_C]

/-! ### `CZ` and `Z` -/

theorem qsC_hiZ : Commute 𝐂 (his p g 𝐙) := by
  have e : his p g 𝐙 = his p g (𝐇 ^ 2) * his p g 𝐒 * his p g (𝐇 ^ 2) * (his p g 𝐒)⁻¹ := by
    rw [qsZ_eq]; simp only [map_mul, map_inv]
  rw [e]; exact alg_comm_Z qs_hiH2_C qsC_hiS

theorem qsC_loS : Commute 𝐂 (los p g 𝐒) := by
  have h := (qsC_hiS (p := p) (g := g)).map (MulAut.conj 𝐖)
  simp only [MulAut.conj_apply] at h
  rwa [qsW_C, qsW_hi] at h

theorem qsC_loZ : Commute 𝐂 (los p g 𝐙) := by
  have h := (qsC_hiZ (p := p) (g := g)).map (MulAut.conj 𝐖)
  simp only [MulAut.conj_apply] at h
  rwa [qsW_C, qsW_hi] at h

/-! ### `CX` -/

theorem qsCX_loX : Commute 𝐂𝐗 (los p g 𝐗) := by
  have e : los p g 𝐗 = (los p g 𝐇)⁻¹ * los p g 𝐙 * los p g 𝐇 := by
    rw [qs_X_eq_conj]; simp only [map_mul, map_inv]
  rw [qsCX_eq, e]
  exact alg_conj_comm qsC_loZ

theorem qs_hiH2_CX : his p g (𝐇 ^ 2) * 𝐂𝐗 * (his p g (𝐇 ^ 2))⁻¹ = 𝐂𝐗⁻¹ := by
  rw [qsCX_eq, alg_conj_through (lohi_comm 𝐇 (𝐇 ^ 2)).symm qs_hiH2_C]; gnorm

theorem qs_loH2_CX : los p g (𝐇 ^ 2) * 𝐂𝐗 * (los p g (𝐇 ^ 2))⁻¹ = 𝐂𝐗⁻¹ := by
  have hc : Commute (los p g (𝐇 ^ 2)) (los p g 𝐇) := by
    rw [map_pow]; exact (Commute.refl _).pow_left 2
  rw [qsCX_eq, alg_conj_through hc qs_loH2_C]; gnorm

theorem qs_C12' : 𝐂𝐗⁻¹ * los p g 𝐒 * 𝐂𝐗 = his p g 𝐒 * los p g 𝐒 * 𝐂 := by
  rw [← qs_C12]; gnorm

theorem qs_CX_loS : 𝐂𝐗 * los p g 𝐒 * 𝐂𝐗⁻¹ = his p g 𝐙 * his p g 𝐒 * los p g 𝐒 * 𝐂⁻¹ := by
  have ht : his p g (𝐇 ^ 2) * his p g 𝐒 * (his p g (𝐇 ^ 2))⁻¹ = his p g 𝐙 * his p g 𝐒 := by
    have := congrArg (his p g) (qs_HSH (p := p) (g := g))
    simpa only [map_mul, map_inv] using this
  exact alg_cx_conj qs_C12' qs_hiH2_CX (lohi_comm 𝐒 (𝐇 ^ 2)).symm ht qs_hiH2_C

theorem qs_CX_loZ : 𝐂𝐗⁻¹ * los p g 𝐙 * 𝐂𝐗 = his p g 𝐙 * los p g 𝐙 := by
  have hB2 : los p g (𝐇 ^ 2) * los p g (𝐇 ^ 2) = 1 := by rw [← map_mul, qs_H4, map_one]
  have hBt : los p g (𝐇 ^ 2) * (his p g 𝐙 * his p g 𝐒) * (los p g (𝐇 ^ 2))⁻¹ =
      his p g 𝐙 * his p g 𝐒 := by
    rw [← map_mul]; exact conj_of_commute (lohi_comm _ _)
  have hBs : los p g (𝐇 ^ 2) * los p g 𝐒 * (los p g (𝐇 ^ 2))⁻¹ = los p g 𝐙 * los p g 𝐒 := by
    have := congrArg (los p g) (qs_HSH (p := p) (g := g))
    simpa only [map_mul, map_inv] using this
  have hzb : los p g 𝐙 = los p g (𝐇 ^ 2) * los p g 𝐒 * los p g (𝐇 ^ 2) * (los p g 𝐒)⁻¹ := by
    rw [qsZ_eq]; simp only [map_mul, map_inv]
  exact alg_cx_Z hB2 qs_loH2_CX qs_CX_loS qs_C12' hBt hBs qs_loH2_C (lohi_comm 𝐙 𝐒).symm hzb

/-! ### `CZ` and `X` -/

theorem qs_SZ_comm : Commute 𝐒 𝐙 := qs_SZ

theorem qs_C_loX : 𝐂 * los p g 𝐗 * 𝐂⁻¹ = los p g 𝐗 * his p g 𝐙 := by
  have hsX : los p g 𝐒 * los p g 𝐗 * (los p g 𝐒)⁻¹ = los p g 𝐗 * los p g 𝐙 := by
    have := congrArg (los p g) (qs_SXS (p := p) (g := g))
    simpa only [map_mul, map_inv] using this
  have hsX' : (los p g 𝐒)⁻¹ * los p g 𝐗 * los p g 𝐒 = los p g 𝐗 * (los p g 𝐙)⁻¹ := by
    have := congrArg (los p g) (qs_SXS' (p := p) (g := g))
    simpa only [map_mul, map_inv] using this
  exact alg_cz_X qs_C12 qsCX_loX hsX hsX' qs_CX_loZ (lohi_comm 𝐗 𝐒).symm
    (qs_SZ_comm.map (his p g)) (lohi_comm 𝐙 𝐒).symm (lohi_comm 𝐒 𝐙) (qs_SZ_comm.map (los p g))
    (lohi_comm 𝐙 𝐙).symm

theorem qs_C_hiX : 𝐂 * his p g 𝐗 * 𝐂⁻¹ = his p g 𝐗 * los p g 𝐙 := by
  calc 𝐂 * his p g 𝐗 * 𝐂⁻¹ = (𝐖 * 𝐂 * 𝐖⁻¹) * (𝐖 * los p g 𝐗 * 𝐖⁻¹) * (𝐖 * 𝐂 * 𝐖⁻¹)⁻¹ := by
        rw [qsW_C, qsW_lo]
    _ = 𝐖 * (𝐂 * los p g 𝐗 * 𝐂⁻¹) * 𝐖⁻¹ := by gnorm
    _ = (𝐖 * los p g 𝐗 * 𝐖⁻¹) * (𝐖 * his p g 𝐙 * 𝐖⁻¹) := by rw [qs_C_loX]; gnorm
    _ = his p g 𝐗 * los p g 𝐙 := by rw [qsW_lo, qsW_hi]

end QCert.QuditClifford
