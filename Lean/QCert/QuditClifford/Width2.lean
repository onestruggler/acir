/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The local facts on two wires

`lf2 : LF2 p g`, from the rules on one and two wires.

In `Gh p g 2` the classes `xh t = CX^t` and `yh t = CX'^t` (`CX'` with
control on wire 0) act on the `X` exponents as the elementary matrices of
`SL₂(ℤ_p)`: the multipliers rescale them (`lo_Mq_xh`, `hi_Mq_xh`,
`lo_Mq_yh`, `hi_Mq_yh`), the swap exchanges them (`SW_xh`), `H ⊗ H` turns
`xh t` into `yh (-t)` (`HH_xh`), and `x(-1) y(1) = SWAP H₁² x(1)` (`xy_SW`,
from `SW_eq`).

* `bS`, `bOne`: the box `B_u` conjugates `S` on wire 1, and the one-qudit
  gates on wire 0 up to the stabiliser of `Z` on one wire (`lf1`), into
  the stabiliser of `Z` on wire 0;
* `czS0`: (C8) moved to wire 0;
* `heis`: `CZ` composes with `c(P)` as the Heisenberg group law, with no
  correction (`heis_eq`);
* `cz`: `CZ` moves the section into `J p g 1`.  Up to the swap symmetry
  (`QPC_of_swap`, from `QP_SW`) there are three cases: `u` on wire 0 only
  (`QPC_I`), a `Z` power on wire 1 (`QPC_III`), and `X` powers on both
  wires (`QPC_XX`, where the correction is `H S^e H⁻¹`, conjugated by a
  multiplier, on wire 1).

Every case was checked on symplectic matrices for `p = 3, 5, 7` first.
-/
import QCert.QuditClifford.Width2Kit

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-! ### Group identities -/

section Alg

variable {G : Type*} [Group G]

theorem alg_conjA {C T K L X : G} (hS : C * T = T * C) (hK : K * C * K⁻¹ = X⁻¹) :
    (T * K⁻¹ * L⁻¹)⁻¹ * C * (T * K⁻¹ * L⁻¹) = (L * X * L⁻¹)⁻¹ := by
  calc (T * K⁻¹ * L⁻¹)⁻¹ * C * (T * K⁻¹ * L⁻¹)
      = L * (K * (T⁻¹ * (C * T)) * K⁻¹) * L⁻¹ := by group
    _ = L * (K * C * K⁻¹) * L⁻¹ := by rw [hS]; group
    _ = (L * X * L⁻¹)⁻¹ := by rw [hK]; group

theorem alg_conjB {C T K N Y : G} (hY : K⁻¹ * (N * C * N⁻¹) * K = Y) :
    T * K⁻¹ * N * C * (T * K⁻¹ * N)⁻¹ = T * Y * T⁻¹ := by
  rw [← hY]; group

theorem alg_sw1 {s h l : G} (hss : s * s = 1) (h1 : s * h * s⁻¹ = l) : (h * s)⁻¹ * s * l = 1 := by
  calc (h * s)⁻¹ * s * l = s⁻¹ * h⁻¹ * (s * s) * h * s⁻¹ := by rw [← h1]; group
    _ = s⁻¹ * s⁻¹ := by rw [hss]; group
    _ = (s * s)⁻¹ := by group
    _ = 1 := by rw [hss, inv_one]

theorem alg_sw2 {s h l : G} (hss : s * s = 1) (h1 : s * h * s⁻¹ = l) : l⁻¹ * s * (h * s) = 1 := by
  calc l⁻¹ * s * (h * s) = s * s := by rw [← h1]; group
    _ = 1 := hss

theorem alg_sw3 {s ha1 la1 la0 ha0 u x y : G} (h1 : s * ha1 = la1 * s) (h2 : s * la0 = ha0 * s)
    (h3 : la1 * ha0 = ha0 * la1) (hs : s = u * x * y * x) (hu : u * x * u⁻¹ = x⁻¹) :
    (ha0 * (la1 * u * x))⁻¹ * s * (ha1 * (la0 * u * x)) = y * u := by
  calc (ha0 * (la1 * u * x))⁻¹ * s * (ha1 * (la0 * u * x))
      = x⁻¹ * u⁻¹ * la1⁻¹ * ha0⁻¹ * (s * ha1) * la0 * u * x := by group
    _ = x⁻¹ * u⁻¹ * la1⁻¹ * ha0⁻¹ * la1 * (s * la0) * u * x := by rw [h1]; group
    _ = x⁻¹ * u⁻¹ * (la1⁻¹ * ha0⁻¹ * (la1 * ha0)) * s * u * x := by rw [h2]; group
    _ = x⁻¹ * u⁻¹ * s * u * x := by rw [h3]; group
    _ = y * (x * (u * x * u⁻¹) * u) := by rw [hs]; group
    _ = y * u := by rw [hu]; group

theorem alg_Ib {N la u x c X M : G} (hc : la * N = N * la) (hla : la⁻¹ * c * la = X)
    (hun : u⁻¹ * N⁻¹ = M) (hmx : M * X = x * M) : (N * (la * u * x))⁻¹ * c * la = M := by
  calc (N * (la * u * x))⁻¹ * c * la = x⁻¹ * u⁻¹ * (N * la)⁻¹ * c * la := by group
    _ = x⁻¹ * u⁻¹ * (la * N)⁻¹ * c * la := by rw [hc]
    _ = x⁻¹ * (u⁻¹ * N⁻¹) * (la⁻¹ * c * la) := by group
    _ = x⁻¹ * (M * X) := by rw [hun, hla]; group
    _ = M := by rw [hmx]; group

theorem alg_IIIb1 {la N u x c X M Y : G} (hc : N * la = la * N) (hla : la⁻¹ * c * la = X)
    (hnu : N * u = M) (hmx : M * x = Y * M) (hxy : X * Y = 1) :
    la⁻¹ * c * (N * (la * u * x)) = M := by
  calc la⁻¹ * c * (N * (la * u * x)) = la⁻¹ * c * (N * la) * u * x := by group
    _ = la⁻¹ * c * (la * N) * u * x := by rw [hc]
    _ = (la⁻¹ * c * la) * (N * u) * x := by group
    _ = X * (M * x) := by rw [hla, hnu]; group
    _ = M := by rw [hmx, ← mul_assoc, hxy, one_mul]

theorem alg_IIIb2 {ng nd la u x c X m1 m2 m3 X' Y : G} (hc1 : la * ng = ng * la)
    (hc2 : nd * la = la * nd) (hla : la⁻¹ * c * la = X) (h1 : u⁻¹ * ng⁻¹ = m1)
    (h2 : nd * u = m2) (h3 : m1 * X = X' * m1) (h4 : m1 * m2 = m3) (h5 : m3 * x = Y * m3)
    (h6 : x⁻¹ * X' * Y = 1) :
    (ng * (la * u * x))⁻¹ * c * (nd * (la * u * x)) = m3 := by
  calc (ng * (la * u * x))⁻¹ * c * (nd * (la * u * x))
      = x⁻¹ * u⁻¹ * (ng * la)⁻¹ * c * (nd * la) * u * x := by group
    _ = x⁻¹ * u⁻¹ * (la * ng)⁻¹ * c * (la * nd) * u * x := by rw [hc1, hc2]
    _ = x⁻¹ * (u⁻¹ * ng⁻¹) * (la⁻¹ * c * la) * (nd * u) * x := by group
    _ = x⁻¹ * (m1 * X) * m2 * x := by rw [h1, hla, h2]; group
    _ = x⁻¹ * X' * (m1 * m2) * x := by rw [h3]; group
    _ = x⁻¹ * X' * (m3 * x) := by rw [h4]; group
    _ = m3 := by rw [h5, ← mul_assoc, h6, one_mul]

theorem alg_conj3 (n la u x c : G) :
    (n * (la * u * x))⁻¹ * c * (n * (la * u * x)) =
      x⁻¹ * (u⁻¹ * (la⁻¹ * (n⁻¹ * c * n) * la) * u) * x := by
  group

theorem alg_bS {la u x y : G} (h1 : la * y = y * la) (h2 : u * y = y * u) (h3 : x * y = y * x) :
    (la * u * x)⁻¹ * y * (la * u * x) = y := by
  calc (la * u * x)⁻¹ * y * (la * u * x) = x⁻¹ * u⁻¹ * la⁻¹ * (y * la) * u * x := by group
    _ = x⁻¹ * u⁻¹ * (y * u) * x := by rw [← h1]; group
    _ = x⁻¹ * (y * x) := by rw [← h2]; group
    _ = y := by rw [← h3]; group

theorem alg_bOne {la' la ly u x : G} (hu : u * (la'⁻¹ * ly * la) = (la'⁻¹ * ly * la) * u) :
    (la' * u * x)⁻¹ * ly * (la * u * x) = x⁻¹ * (la'⁻¹ * ly * la) * x := by
  calc (la' * u * x)⁻¹ * ly * (la * u * x) = x⁻¹ * (u⁻¹ * ((la'⁻¹ * ly * la) * u)) * x := by group
    _ = x⁻¹ * (la'⁻¹ * ly * la) * x := by rw [← hu]; group

theorem alg_heis {L T W y C D : G} (h1 : L * T = T * L) (h2 : C * T = T * C)
    (hD : W⁻¹ * L⁻¹ * C = D) (key : y⁻¹ * D * y = W⁻¹) :
    (L * (T * W * y * (T * W)⁻¹))⁻¹ * (C * (T * y * T⁻¹)) = 1 := by
  have hc : T⁻¹ * L⁻¹ * C * T = L⁻¹ * C := by
    calc T⁻¹ * L⁻¹ * C * T = (L * T)⁻¹ * (C * T) := by group
      _ = (T * L)⁻¹ * (T * C) := by rw [h1, h2]
      _ = L⁻¹ * C := by group
  calc (L * (T * W * y * (T * W)⁻¹))⁻¹ * (C * (T * y * T⁻¹))
      = T * W * y⁻¹ * W⁻¹ * (T⁻¹ * L⁻¹ * C * T) * y * T⁻¹ := by group
    _ = T * W * (y⁻¹ * (W⁻¹ * L⁻¹ * C) * y) * T⁻¹ := by rw [hc]; group
    _ = 1 := by rw [hD, key]; group

theorem alg_prod3 {a1 a2 a3 b1 b2 b3 : G} (c11 : b1 * a1 = a1 * b1) (c21 : b2 * a1 = a1 * b2)
    (c31 : b3 * a1 = a1 * b3) (c22 : b2 * a2 = a2 * b2) (c32 : b3 * a2 = a2 * b3)
    (c33 : b3 * a3 = a3 * b3) :
    b1 * b2 * b3 * (a1 * a2 * a3) = (a1 * b1) * (a2 * b2) * (a3 * b3) := by
  calc b1 * b2 * b3 * (a1 * a2 * a3) = b1 * b2 * (b3 * a1) * a2 * a3 := by group
    _ = b1 * (b2 * a1) * b3 * a2 * a3 := by rw [c31]; group
    _ = (b1 * a1) * b2 * b3 * a2 * a3 := by rw [c21]; group
    _ = a1 * b1 * b2 * (b3 * a2) * a3 := by rw [c11]; group
    _ = a1 * b1 * (b2 * a2) * b3 * a3 := by rw [c32]; group
    _ = a1 * b1 * a2 * b2 * (b3 * a3) := by rw [c22]; group
    _ = (a1 * b1) * (a2 * b2) * (a3 * b3) := by rw [c33]; group

theorem alg_inner {P Q N D k L kk LL yy ZZ : G} (hP : P * D = D * P) (hD : D = k⁻¹ * L * k)
    (hk : Q * k * Q⁻¹ = kk) (hL : Q * L * Q⁻¹ = LL) (hkk : N⁻¹ * kk * N = yy)
    (hLL : N⁻¹ * LL * N = ZZ) :
    (P * Q⁻¹ * N)⁻¹ * D * (P * Q⁻¹ * N) = yy⁻¹ * ZZ * yy := by
  calc (P * Q⁻¹ * N)⁻¹ * D * (P * Q⁻¹ * N) = N⁻¹ * (Q * (P⁻¹ * (D * P)) * Q⁻¹) * N := by group
    _ = N⁻¹ * (Q * D * Q⁻¹) * N := by rw [← hP]; group
    _ = N⁻¹ * ((Q * k * Q⁻¹)⁻¹ * (Q * L * Q⁻¹) * (Q * k * Q⁻¹)) * N := by rw [hD]; group
    _ = (N⁻¹ * kk * N)⁻¹ * (N⁻¹ * LL * N) * (N⁻¹ * kk * N) := by rw [hk, hL]; group
    _ = yy⁻¹ * ZZ * yy := by rw [hkk, hLL]

theorem alg_XX_pre {x u la ha ls hs c : G} (hc : ls * ha = ha * ls) :
    ((hs * ha) * ((ls * la) * u * x))⁻¹ * c * (ha * (la * u * x)) =
      x⁻¹ * u⁻¹ * ((ha * la)⁻¹ * (ls⁻¹ * hs⁻¹ * c) * (ha * la)) * u * x := by
  calc ((hs * ha) * ((ls * la) * u * x))⁻¹ * c * (ha * (la * u * x))
      = x⁻¹ * u⁻¹ * la⁻¹ * (ha * ls)⁻¹ * hs⁻¹ * c * ha * la * u * x := by group
    _ = x⁻¹ * u⁻¹ * la⁻¹ * (ls * ha)⁻¹ * hs⁻¹ * c * ha * la * u * x := by rw [hc]
    _ = x⁻¹ * u⁻¹ * ((ha * la)⁻¹ * (ls⁻¹ * hs⁻¹ * c) * (ha * la)) * u * x := by group

theorem alg_XX {x y u s z zh : G} (hu1 : u⁻¹ * y⁻¹ * u = y) (hu2 : u⁻¹ * y * u = y⁻¹)
    (hxy : x⁻¹ * y = s * u * x) (hxz : x * z = z * x) (huz : u * z = z * u)
    (hs : s * z * s⁻¹ = zh) : x⁻¹ * u⁻¹ * (y⁻¹ * z * y) * u * x = zh := by
  have huz' : u⁻¹ * z * u = z := by rw [mul_assoc, ← huz, inv_mul_cancel_left]
  have huz'' : u * z * u⁻¹ = z := by rw [huz, mul_inv_cancel_right]
  have hxz' : x * z * x⁻¹ = z := by rw [hxz, mul_inv_cancel_right]
  calc x⁻¹ * u⁻¹ * (y⁻¹ * z * y) * u * x
      = x⁻¹ * (u⁻¹ * y⁻¹ * u) * (u⁻¹ * z * u) * (u⁻¹ * y * u) * x := by group
    _ = x⁻¹ * y * z * y⁻¹ * x := by rw [hu1, hu2, huz']
    _ = (x⁻¹ * y) * z * (x⁻¹ * y)⁻¹ := by group
    _ = s * u * (x * z * x⁻¹) * u⁻¹ * s⁻¹ := by rw [hxy]; group
    _ = s * (u * z * u⁻¹) * s⁻¹ := by rw [hxz']; group
    _ = zh := by rw [huz'']; exact hs

theorem alg_comm_conj {m X Y : G} (h : X * Y = Y * X) :
    (m * X * m⁻¹) * (m * Y * m⁻¹) = (m * Y * m⁻¹) * (m * X * m⁻¹) := by
  calc (m * X * m⁻¹) * (m * Y * m⁻¹) = m * (X * Y) * m⁻¹ := by group
    _ = m * (Y * X) * m⁻¹ := by rw [h]
    _ = (m * Y * m⁻¹) * (m * X * m⁻¹) := by group

end Alg

/-! ### The two wires as homomorphisms -/

theorem lo_mul (x y : Gh p g 1) : lo p g (x * y) = lo p g x * lo p g y := map_mul _ x y
theorem lo_inv (x : Gh p g 1) : lo p g x⁻¹ = (lo p g x)⁻¹ := map_inv _ x
theorem lo_one : lo p g 1 = 1 := map_one _
theorem lo_pow (x : Gh p g 1) (n : ℕ) : lo p g (x ^ n) = lo p g x ^ n := map_pow _ x n
theorem hi_mul (x y : Gh p g 1) : hi p g (x * y) = hi p g x * hi p g y := map_mul _ x y
theorem hi_inv (x : Gh p g 1) : hi p g x⁻¹ = (hi p g x)⁻¹ := map_inv _ x
theorem hi_one : hi p g 1 = 1 := map_one _
theorem hi_pow (x : Gh p g 1) (n : ℕ) : hi p g (x ^ n) = hi p g x ^ n := map_pow _ x n

/-! ### One qudit -/

theorem neg_one_ne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.2 one_ne_zero

theorem Mq_neg_one_inv : (Mq p g (-1))⁻¹ = Mq p g (-1) := by
  rw [Mq_inv neg_one_ne, inv_neg, inv_one]

theorem Hsq_inv : (Hq p g ^ 2)⁻¹ = Hq p g ^ 2 := by rw [Hq_sq, Mq_neg_one_inv]

theorem HSH_eq (e : ZMod p) : Hq p g * Sq p g e * (Hq p g)⁻¹ = (Hq p g)⁻¹ * Sq p g e * Hq p g := by
  have h : Sq p g e * (Hq p g * Hq p g) = (Hq p g * Hq p g) * Sq p g e := by
    rw [← sq]; exact Sq_comm_Hsq e
  calc Hq p g * Sq p g e * (Hq p g)⁻¹ = (Hq p g)⁻¹ * ((Hq p g * Hq p g) * Sq p g e) * (Hq p g)⁻¹ := by
        group
    _ = (Hq p g)⁻¹ * (Sq p g e * (Hq p g * Hq p g)) * (Hq p g)⁻¹ := by rw [h]
    _ = (Hq p g)⁻¹ * Sq p g e * Hq p g := by group

theorem Aq_ne {α β : ZMod p} (hα : α ≠ 0) :
    qh p g 1 (Acirc p (α, β)) = Sq p g (β / α) * Hq p g ^ 3 * Mq p g α⁻¹ := by
  rw [Acirc_eq]; exact if_neg hα

theorem Aq_zero (β : ZMod p) : qh p g 1 (Acirc p (0, β)) = Mq p g β⁻¹ := by
  rw [Acirc_eq]; exact if_pos rfl

theorem Aq_shift {a b c : ZMod p} (ha : a ≠ 0) :
    qh p g 1 (Acirc p (a, b + c)) = Sq p g (c / a) * qh p g 1 (Acirc p (a, b)) := by
  rw [Aq_ne ha, Aq_ne ha, add_div, add_comm (b / a), Sq_add]
  simp only [mul_assoc]

/-! ### Elementary matrices -/

variable (p g) in
/-- `CX^t`: wire 0 gains `t` times wire 1 in the `X` exponents. -/
noncomputable def xh (t : ZMod p) : Gh p g 2 := CXh p g ^ t.val

variable (p g) in
/-- `CX'^t`: wire 1 gains `t` times wire 0 in the `X` exponents. -/
noncomputable def yh (t : ZMod p) : Gh p g 2 := CXh' p g ^ t.val

theorem CXh'_pow_p : CXh' p g ^ p = 1 := by
  rw [CXh', conj_pow_inv, Cz_pow_p, mul_one, inv_mul_cancel]

theorem xh_add (a b : ZMod p) : xh p g (a + b) = xh p g a * xh p g b := pow_val_add CXh_pow_p a b
theorem xh_neg (a : ZMod p) : xh p g (-a) = (xh p g a)⁻¹ := pow_val_neg CXh_pow_p a
theorem xh_zero : xh p g 0 = 1 := pow_val_zero _
theorem xh_one : xh p g 1 = CXh p g := pow_val_one CXh_pow_p
theorem yh_neg (a : ZMod p) : yh p g (-a) = (yh p g a)⁻¹ := pow_val_neg CXh'_pow_p a
theorem yh_one : yh p g 1 = CXh' p g := pow_val_one CXh'_pow_p

theorem yh_mem_J (t : ZMod p) : yh p g t ∈ J p g 1 := Subgroup.pow_mem _ CXh'_mem_J _

theorem lo_Mq_xh {a : ZMod p} (ha : a ≠ 0) (t : ZMod p) :
    lo p g (Mq p g a) * xh p g t * (lo p g (Mq p g a))⁻¹ = xh p g (a * t) := by
  rw [xh, xh, ← conj_pow, lo_Mq_conj_CX ha, ← pow_val_mul CXh_pow_p]

theorem hi_Mq_xh {a : ZMod p} (ha : a ≠ 0) (t : ZMod p) :
    hi p g (Mq p g a) * xh p g t * (hi p g (Mq p g a))⁻¹ = xh p g (a⁻¹ * t) := by
  rw [xh, xh, ← conj_pow, hi_Mq_conj_CX ha, ← pow_val_mul CXh_pow_p]

theorem SW_xh (t : ZMod p) : SWh p g * xh p g t * (SWh p g)⁻¹ = yh p g t := by
  rw [xh, yh, ← conj_pow, SW_CX]

theorem lo_Mq_yh {a : ZMod p} (ha : a ≠ 0) (t : ZMod p) :
    lo p g (Mq p g a) * yh p g t * (lo p g (Mq p g a))⁻¹ = yh p g (a⁻¹ * t) := by
  rw [← SW_hi, ← SW_xh, ← SW_xh, ← hi_Mq_xh ha]; group

theorem hi_Mq_yh {a : ZMod p} (ha : a ≠ 0) (t : ZMod p) :
    hi p g (Mq p g a) * yh p g t * (hi p g (Mq p g a))⁻¹ = yh p g (a * t) := by
  rw [← SW_lo, ← SW_xh, ← SW_xh, ← lo_Mq_xh ha]; group

/-- `H²` on wire 1 negates `CX'`. -/
theorem U_conj_yh (t : ZMod p) :
    (hi p g (Hq p g ^ 2))⁻¹ * yh p g t * hi p g (Hq p g ^ 2) = yh p g (-t) := by
  calc (hi p g (Hq p g ^ 2))⁻¹ * yh p g t * hi p g (Hq p g ^ 2)
      = hi p g (Mq p g (-1)) * yh p g t * (hi p g (Mq p g (-1)))⁻¹ := by
        rw [Hq_sq, ← hi_inv, Mq_neg_one_inv]
    _ = yh p g (-t) := by rw [hi_Mq_yh neg_one_ne, neg_one_mul]

theorem U_conj_xh : hi p g (Hq p g ^ 2) * xh p g 1 * (hi p g (Hq p g ^ 2))⁻¹ = (xh p g 1)⁻¹ := by
  rw [Hq_sq, hi_Mq_xh neg_one_ne, inv_neg, inv_one, mul_one, xh_neg]

theorem SW_xy : SWh p g = hi p g (Hq p g ^ 2) * xh p g 1 * yh p g (-1) * xh p g 1 := by
  rw [xh_one, yh_neg, yh_one]; exact SW_eq

/-- `x(-1) y(1) = SWAP H₁² x(1)`. -/
theorem xy_SW : (xh p g 1)⁻¹ * yh p g 1 = SWh p g * hi p g (Hq p g ^ 2) * xh p g 1 := by
  have h := SW_xy (p := p) (g := g)
  have e2 : yh p g 1 = (yh p g (-1))⁻¹ := by rw [yh_neg, inv_inv]
  rw [e2]
  conv_rhs => rw [← SW_inv, h]
  group

/-- `H ⊗ H` turns `CX` into `CX'⁻¹`. -/
theorem HH_xh (k : ZMod p) :
    (lo p g (Hq p g) * hi p g (Hq p g)) * xh p g k * (lo p g (Hq p g) * hi p g (Hq p g))⁻¹ =
      yh p g (-k) := by
  have h1 : lo p g (Hq p g) * xh p g 1 * (lo p g (Hq p g))⁻¹ = Cz p g := by
    rw [xh_one, CXh_eq]; group
  have h2 : hi p g (Hq p g) * Cz p g * (hi p g (Hq p g))⁻¹ = yh p g (-1) := by
    have e : hi p g (Mq p g (-1)) = hi p g (Hq p g) * hi p g (Hq p g) := by
      rw [← Hq_sq, hi_pow, sq]
    have := hi_Mq_yh (p := p) (g := g) neg_one_ne (1 : ZMod p)
    rw [e, yh_one, CXh', neg_one_mul] at this
    rw [← this]; group
  have h3 : (lo p g (Hq p g) * hi p g (Hq p g)) * xh p g 1 *
      (lo p g (Hq p g) * hi p g (Hq p g))⁻¹ = yh p g (-1) := by
    calc (lo p g (Hq p g) * hi p g (Hq p g)) * xh p g 1 * (lo p g (Hq p g) * hi p g (Hq p g))⁻¹
        = (hi p g (Hq p g) * lo p g (Hq p g)) * xh p g 1 *
            (hi p g (Hq p g) * lo p g (Hq p g))⁻¹ := by rw [lo_hi_comm]
      _ = hi p g (Hq p g) * (lo p g (Hq p g) * xh p g 1 * (lo p g (Hq p g))⁻¹) *
            (hi p g (Hq p g))⁻¹ := by group
      _ = yh p g (-1) := by rw [h1, h2]
  rw [show xh p g k = xh p g 1 ^ k.val by rw [xh_one]; rfl, ← conj_pow, h3, yh, yh,
    ← pow_val_mul CXh'_pow_p, neg_one_mul]

theorem HH_lo (e : ZMod p) :
    (lo p g (Hq p g) * hi p g (Hq p g)) * lo p g (Sq p g e) * (lo p g (Hq p g) * hi p g (Hq p g))⁻¹ =
      lo p g (Hq p g * Sq p g e * (Hq p g)⁻¹) := by
  calc (lo p g (Hq p g) * hi p g (Hq p g)) * lo p g (Sq p g e) *
        (lo p g (Hq p g) * hi p g (Hq p g))⁻¹
      = lo p g (Hq p g) * (hi p g (Hq p g) * lo p g (Sq p g e)) * (hi p g (Hq p g))⁻¹ *
          (lo p g (Hq p g))⁻¹ := by group
    _ = lo p g (Hq p g) * (lo p g (Sq p g e) * hi p g (Hq p g)) * (hi p g (Hq p g))⁻¹ *
          (lo p g (Hq p g))⁻¹ := by rw [← lo_hi_comm]
    _ = lo p g (Hq p g * Sq p g e * (Hq p g)⁻¹) := by rw [lo_mul, lo_mul, lo_inv]; group

/-- `CX` commutes with `H S^e H⁻¹` on wire 0. -/
theorem x1_comm (e : ZMod p) :
    xh p g 1 * lo p g (Hq p g * Sq p g e * (Hq p g)⁻¹) =
      lo p g (Hq p g * Sq p g e * (Hq p g)⁻¹) * xh p g 1 := by
  have h := (Cz_comm_loSq (p := p) (g := g) e).eq
  rw [HSH_eq, xh_one, CXh_eq, lo_mul, lo_mul, lo_inv]
  calc _ = (lo p g (Hq p g))⁻¹ * (Cz p g * lo p g (Sq p g e)) * lo p g (Hq p g) := by group
    _ = (lo p g (Hq p g))⁻¹ * (lo p g (Sq p g e) * Cz p g) * lo p g (Hq p g) := by rw [h]
    _ = _ := by group

theorem x_comm_Y (t e : ZMod p) :
    xh p g t * lo p g (Hq p g * Sq p g e * (Hq p g)⁻¹) =
      lo p g (Hq p g * Sq p g e * (Hq p g)⁻¹) * xh p g t := by
  have h' : Commute (CXh p g) (lo p g (Hq p g * Sq p g e * (Hq p g)⁻¹)) := by
    rw [← xh_one]; exact x1_comm e
  exact (h'.pow_left t.val).eq

/-! ### Sections on two wires -/

theorem bh_zero : bh p g 0 = SWh p g := by
  rw [bh, bcirc, if_pos rfl]; rfl

theorem bh_ne {u : ZMod p × ZMod p} (hu : u ≠ 0) :
    bh p g u = lo p g (qh p g 1 (Acirc p u)) * hi p g (Hq p g ^ 2) * xh p g 1 := by
  have e : qh p g 2 (Circuit.shift (H ^ 2)) = hi p g (Hq p g ^ 2) := by
    rw [← ιh_qh, map_pow]
  rw [bh, bcirc, if_neg hu, map_mul, map_mul, e, xh_one]; rfl

theorem s1_lo (v : V p 2) (h : v 1 = 0) : s₁h p g 1 v = lo p g (qh p g 1 (Acirc p (v 0))) := by
  have ht : Fin.tail v = 0 := by funext i; rw [Subsingleton.elim i 0]; exact h
  rw [s₁h_tail0 1 v ht]

theorem s1_hi (v : V p 2) (h : v 1 ≠ 0) :
    s₁h p g 1 v = hi p g (qh p g 1 (Acirc p (v 1))) * bh p g (v 0) := by
  have ht : Fin.tail v ≠ 0 := fun ht => h (congrFun ht 0)
  exact s₁h_one v ht

theorem cz0 (u : V p 2) :
    σGen p (Gen.gate2 (n := 0) Gate.CZ) u 0 = ((u 0).1, (u 0).2 + (u 1).1) := by
  rw [σGen_CZ]; rfl

theorem cz1 (u : V p 2) :
    σGen p (Gen.gate2 (n := 0) Gate.CZ) u 1 = ((u 1).1, (u 1).2 + (u 0).1) := by
  rw [σGen_CZ]; rfl

theorem σSW (u : V p 2) : σh 2 (SWh p g) u = ![u 1, u 0] := σC2_SWAP p u

/-! ### `S` on wire 1 and the one-qudit gates on wire 0 -/

theorem lf2_bS (u : ZMod p × ZMod p) : (bh p g u)⁻¹ * ιh 1 (S0h p g 0) * bh p g u ∈ J p g 1 := by
  have hS : ιh 1 (S0h p g 0) = hi p g (Sq p g 1) := by rw [Sq_one]; rfl
  rw [hS]
  by_cases hu : u = 0
  · subst hu
    rw [bh_zero, SW_inv]
    have h := SW_hi (p := p) (g := g) (Sq p g 1)
    rw [SW_inv] at h
    rw [h, Sq_one]
    exact S0h_mem_J 1
  · have hU : hi p g (Hq p g ^ 2) * hi p g (Sq p g 1) = hi p g (Sq p g 1) * hi p g (Hq p g ^ 2) := by
      rw [← hi_mul, ← hi_mul, Sq_comm_Hsq]
    have hX : xh p g 1 * hi p g (Sq p g 1) = hi p g (Sq p g 1) * xh p g 1 := by
      rw [xh_one]; exact (CX_comm_hiSq 1).eq
    rw [bh_ne hu, alg_bS (lo_hi_comm _ _) hU hX]
    exact ιh_mem_J _

theorem act1_zero (y : Gate 1) : act1 p y 0 = 0 := by
  cases y <;> exact Prod.ext (by simp [act1]) (by simp [act1])

theorem act1_ne_zero (y : Gate 1) {u : ZMod p × ZMod p} (hu : u ≠ 0) : act1 p y u ≠ 0 := by
  intro h
  apply hu
  obtain ⟨a, b⟩ := u
  cases y with
  | H =>
    have h1 : -b = 0 := congrArg Prod.fst h
    have h2 : a = 0 := congrArg Prod.snd h
    rw [neg_eq_zero] at h1
    exact Prod.ext h2 h1
  | S =>
    have h1 : a = 0 := congrArg Prod.fst h
    have h2 : a + b = 0 := congrArg Prod.snd h
    rw [h1, zero_add] at h2
    exact Prod.ext h1 h2

/-- The stabiliser of `Z` on one wire, on wire 0 and conjugated by `CX`. -/
theorem x_conj_loJ {j : Gh p g 1} (hj : j ∈ J p g 0) :
    (xh p g 1)⁻¹ * lo p g j * xh p g 1 ∈ J p g 1 := by
  let f : Gh p g 1 →* Gh p g 2 := (MulAut.conj (xh p g 1)⁻¹).toMonoidHom.comp (padh 1 1)
  have hf : ∀ z, f z = (xh p g 1)⁻¹ * lo p g z * xh p g 1 := fun z => by
    show (xh p g 1)⁻¹ * padh 1 1 z * ((xh p g 1)⁻¹)⁻¹ = _
    rw [inv_inv]
  rw [← hf]
  refine (Subgroup.closure_le ((J p g 1).comap f)).2 ?_ hj
  rintro _ (⟨z, rfl⟩ | h)
  · rw [Gh_zero_trivial z, map_one, SetLike.mem_coe, Subgroup.mem_comap, map_one]
    exact Subgroup.one_mem _
  · rw [Set.mem_singleton_iff] at h; subst h
    rw [SetLike.mem_coe, Subgroup.mem_comap, hf, xh_one,
      show lo p g (S0h p g 0) = lo p g (qh p g 1 S) from rfl, C12h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ιh_mem_J _) (S0h_mem_J 1)) (CZh_mem_J 0)

theorem lf2_bOne (y : Gate 1) (u : ZMod p × ZMod p) :
    (bh p g (act1 p y u))⁻¹ * qh p g 2 (Circuit.g1 y) * bh p g u ∈ J p g 1 := by
  have hY : qh p g 2 (Circuit.g1 y) = lo p g (qh p g 1 (Circuit.g1 y)) := rfl
  rw [hY]
  by_cases hu : u = 0
  · subst hu
    rw [act1_zero, bh_zero, SW_inv]
    have h := SW_lo (p := p) (g := g) (qh p g 1 (Circuit.g1 y))
    rw [SW_inv] at h
    rw [h]; exact ιh_mem_J _
  · have hcomm : hi p g (Hq p g ^ 2) * ((lo p g (qh p g 1 (Acirc p (act1 p y u))))⁻¹ *
        lo p g (qh p g 1 (Circuit.g1 y)) * lo p g (qh p g 1 (Acirc p u))) =
        ((lo p g (qh p g 1 (Acirc p (act1 p y u))))⁻¹ * lo p g (qh p g 1 (Circuit.g1 y)) *
          lo p g (qh p g 1 (Acirc p u))) * hi p g (Hq p g ^ 2) := by
      rw [← lo_inv, ← lo_mul, ← lo_mul]; exact (lo_hi_comm _ _).symm
    rw [bh_ne (act1_ne_zero y hu), bh_ne hu, alg_bOne hcomm, ← lo_inv, ← lo_mul, ← lo_mul]
    exact x_conj_loJ (lf1 y hu)

/-! ### `CZ` conjugated by the boxes -/

/-- `A_{(α, β)}` on wire 0 conjugates `CZ` to `CX^{-α}`. -/
theorem loA_Cz {α β : ZMod p} (hα : α ≠ 0) :
    (lo p g (qh p g 1 (Acirc p (α, β))))⁻¹ * Cz p g * lo p g (qh p g 1 (Acirc p (α, β))) =
      xh p g (-α) := by
  have hM : lo p g (Mq p g α⁻¹) = (lo p g (Mq p g α))⁻¹ := by rw [← lo_inv, Mq_inv hα]
  have hH : lo p g (Hq p g ^ 3) = (lo p g (Hq p g))⁻¹ := by rw [← Hq_inv, lo_inv]
  have hK : lo p g (Hq p g) * Cz p g * (lo p g (Hq p g))⁻¹ = (xh p g 1)⁻¹ := by
    rw [xh_one]; exact loH_conj_Cz
  rw [Aq_ne hα, lo_mul, lo_mul, hM, hH, alg_conjA (Cz_comm_loSq (β / α)).eq hK, lo_Mq_xh hα,
    mul_one, xh_neg]

/-- `A_{(α, β)}` on wire 1 conjugates `CZ` to a conjugate of `CX'^α`. -/
theorem hiA_Cz {α β : ZMod p} (hα : α ≠ 0) :
    hi p g (qh p g 1 (Acirc p (α, β))) * Cz p g * (hi p g (qh p g 1 (Acirc p (α, β))))⁻¹ =
      hi p g (Sq p g (β / α)) * yh p g α * (hi p g (Sq p g (β / α)))⁻¹ := by
  have hH : hi p g (Hq p g ^ 3) = (hi p g (Hq p g))⁻¹ := by rw [← Hq_inv, hi_inv]
  have hM : hi p g (Mq p g α⁻¹) * Cz p g * (hi p g (Mq p g α⁻¹))⁻¹ = Cz p g ^ α.val := by
    have := hi_Mq_conj' (p := p) (g := g) (inv_ne_zero hα) 1
    rwa [Cz_val_one, one_mul, inv_inv] at this
  have hY : (hi p g (Hq p g))⁻¹ * (hi p g (Mq p g α⁻¹) * Cz p g * (hi p g (Mq p g α⁻¹))⁻¹) *
      hi p g (Hq p g) = yh p g α := by
    rw [hM, yh, CXh', conj_pow_inv]
  rw [Aq_ne hα, hi_mul, hi_mul, hH]
  exact alg_conjB hY

/-! ### The Heisenberg law -/

variable (p g) in
/-- `c(P)` on two wires, as a function of `P`'s component on wire 1. -/
noncomputable def cPf (u : ZMod p × ZMod p) : Gh p g 2 :=
  if u = 0 then 1 else hi p g (qh p g 1 (Acirc p u)) * Cz p g * (hi p g (qh p g 1 (Acirc p u)))⁻¹

theorem cP0_eq (P : V p 1) : cP p g 0 P = cPf p g (P 0) := by
  unfold cP cPf
  by_cases h : P 0 = 0
  · rw [if_pos (eq_zero_of_V1 h), if_pos h]
  · rw [if_neg (fun h' => h (by rw [h']; rfl)), if_neg h]; rfl

theorem cPf_Z (b : ZMod p) : cPf p g (0, b) = Cz p g ^ b.val := by
  unfold cPf
  by_cases hb : b = 0
  · subst hb; rw [if_pos (show ((0 : ZMod p), (0 : ZMod p)) = 0 from rfl), pow_val_zero]
  · rw [if_neg (fun h => hb (congrArg Prod.snd h)), Aq_zero]
    have := hi_Mq_conj' (p := p) (g := g) (inv_ne_zero hb) 1
    rwa [Cz_val_one, one_mul, inv_inv] at this

theorem cPf_X {α β : ZMod p} (hα : α ≠ 0) :
    cPf p g (α, β) = hi p g (Sq p g (β / α)) * yh p g α * (hi p g (Sq p g (β / α)))⁻¹ := by
  unfold cPf
  rw [if_neg (fun h => hα (congrArg Prod.fst h)), hiA_Cz hα]

theorem heis_eq (α β : ZMod p) :
    (lo p g (Sq p g α) * cPf p g (α, β + 1))⁻¹ * (Cz p g * cPf p g (α, β)) = 1 := by
  by_cases hα : α = 0
  · subst hα
    rw [cPf_Z, cPf_Z, Sq_zero, lo_one, one_mul, Cz_val_add, Cz_val_one]
    group
  · rw [cPf_X hα, cPf_X hα]
    have hT : hi p g (Sq p g ((β + 1) / α)) = hi p g (Sq p g (β / α)) * hi p g (Sq p g α⁻¹) := by
      rw [← hi_mul, ← Sq_add, add_div, one_div]
    rw [hT]
    refine alg_heis (D := dgh p g (-α) (-α⁻¹) 1) (lo_hi_comm _ _) (Cz_comm_hiSq _).eq ?_ ?_
    · rw [dgh, Sq_neg, Sq_neg, lo_inv, hi_inv, Cz_val_one, ← mul_inv_rev, ← mul_inv_rev,
        lo_hi_comm]
    · rw [yh, CX'_val_conj_dgh]
      rw [show (-α + -α⁻¹ * α ^ 2 + 2 * 1 * α : ZMod p) = 0 by
          rw [neg_mul, sq, ← mul_assoc, inv_mul_cancel₀ hα, one_mul]; ring,
        show (1 + -α⁻¹ * α : ZMod p) = 0 by rw [neg_mul, inv_mul_cancel₀ hα]; ring]
      rw [dgh, Sq_zero, lo_one, one_mul, pow_val_zero, mul_one, Sq_neg, hi_inv]

theorem lf2_heis (P : V p 1) :
    (S0h p g 1 ^ (P 0).1.val * cP p g 0 (P + eZ p 0))⁻¹ * (CZh p g 0 * cP p g 0 P) ∈ Kst p g 1 := by
  rw [cP0_eq, cP0_eq]
  obtain ⟨α, β, hP⟩ : ∃ α β : ZMod p, P 0 = (α, β) := ⟨_, _, rfl⟩
  have hP' : (P + eZ p 0) 0 = (α, β + 1) := by
    show P 0 + (0, 1) = _
    rw [hP, Prod.mk_add_mk, add_zero]
  rw [hP', hP, show S0h p g 1 = lo p g (qh p g 1 S) from rfl, ← lo_pow]
  convert Subgroup.one_mem (Kst p g 1) using 1
  exact heis_eq α β

/-! ### `CZ` on the sections -/

variable (p g) in
/-- A generator `x` moves the section at `u` into the stabiliser of `Z` on wire 0. -/
def QP (x : Gh p g 2) (u : V p 2) : Prop :=
  (s₁h p g 1 (σh 2 x u))⁻¹ * x * s₁h p g 1 u ∈ J p g 1

variable (p g) in
/-- `QP` for `CZ`, with its action written out. -/
def QPC (u : V p 2) : Prop :=
  (s₁h p g 1 (σGen p (Gen.gate2 (n := 0) Gate.CZ) u))⁻¹ * Cz p g * s₁h p g 1 u ∈ J p g 1

theorem σh_Cz (u : V p 2) : σh 2 (Cz p g) u = σGen p (Gen.gate2 (n := 0) Gate.CZ) u := by
  show σC p 2 (FreeMonoid.of (Gen.gate2 (n := 0) Gate.CZ)) u = _
  rw [σC_of]

theorem QP_Cz_iff (u : V p 2) : QP p g (Cz p g) u ↔ QPC p g u := by
  unfold QP QPC; rw [σh_Cz]

theorem QP_mul {x y : Gh p g 2} {u : V p 2} (hy : QP p g y u) (hx : QP p g x (σh 2 y u)) :
    QP p g (x * y) u := by
  unfold QP at *
  have e : σh 2 (x * y) u = σh 2 x (σh 2 y u) := by
    rw [map_mul, Function.End.mul_def, Function.comp_apply]
  rw [e]
  have e2 : (s₁h p g 1 (σh 2 x (σh 2 y u)))⁻¹ * (x * y) * s₁h p g 1 u =
      ((s₁h p g 1 (σh 2 x (σh 2 y u)))⁻¹ * x * s₁h p g 1 (σh 2 y u)) *
        ((s₁h p g 1 (σh 2 y u))⁻¹ * y * s₁h p g 1 u) := by group
  rw [e2]
  exact Subgroup.mul_mem _ hx hy

theorem QP_SW {u : V p 2} (hu : u ≠ 0) : QP p g (SWh p g) u := by
  unfold QP
  rw [σSW]
  have hw0 : (![u 1, u 0] : V p 2) 0 = u 1 := rfl
  have hw1 : (![u 1, u 0] : V p 2) 1 = u 0 := rfl
  by_cases h1 : u 1 = 0
  · have h0 : u 0 ≠ 0 := fun h0 => hu (V2_ext p h0 h1)
    rw [s1_hi _ (by rw [hw1]; exact h0), hw1, hw0, h1, bh_zero, s1_lo u h1,
      alg_sw1 SW_sq (SW_hi _)]
    exact Subgroup.one_mem _
  · by_cases h0 : u 0 = 0
    · rw [s1_lo _ (by rw [hw1]; exact h0), hw0, s1_hi u h1, h0, bh_zero,
        alg_sw2 SW_sq (SW_hi _)]
      exact Subgroup.one_mem _
    · have h1' : SWh p g * hi p g (qh p g 1 (Acirc p (u 1))) =
          lo p g (qh p g 1 (Acirc p (u 1))) * SWh p g := by
        rw [← SW_hi (qh p g 1 (Acirc p (u 1)))]; group
      have h2' : SWh p g * lo p g (qh p g 1 (Acirc p (u 0))) =
          hi p g (qh p g 1 (Acirc p (u 0))) * SWh p g := by
        rw [← SW_lo (qh p g 1 (Acirc p (u 0)))]; group
      rw [s1_hi _ (by rw [hw1]; exact h0), hw1, hw0, bh_ne h1, s1_hi u h1, bh_ne h0,
        alg_sw3 h1' h2' (lo_hi_comm _ _) SW_xy U_conj_xh]
      exact Subgroup.mul_mem _ (yh_mem_J _) (ιh_mem_J _)

theorem Cz_SW : Cz p g = SWh p g * Cz p g * SWh p g := by
  rw [SW_Cz.eq, mul_assoc, SW_sq, mul_one]

theorem QPC_of_swap {u : V p 2} (hu : u ≠ 0) (h : QPC p g (σh 2 (SWh p g) u)) : QPC p g u := by
  have hsw : σh 2 (SWh p g) u ≠ 0 := σh_ne_zero _ hu
  have h' : QP p g (Cz p g) (σh 2 (SWh p g) u) := (QP_Cz_iff _).2 h
  have key : QP p g (SWh p g * Cz p g * SWh p g) u :=
    QP_mul (QP_SW hu) (QP_mul h' (QP_SW (σh_ne_zero _ hsw)))
  rw [← Cz_SW] at key
  exact (QP_Cz_iff u).1 key

/-- `u` on wire 0 only. -/
theorem QPC_I {u : V p 2} (h1 : u 1 = 0) (h0 : u 0 ≠ 0) : QPC p g u := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ZMod p, u 0 = (a, b) := ⟨_, _, rfl⟩
  have e0 : σGen p (Gen.gate2 (n := 0) Gate.CZ) u 0 = (a, b) := by
    rw [cz0, h1, hab] <;> simp
  have e1 : σGen p (Gen.gate2 (n := 0) Gate.CZ) u 1 = (0, a) := by
    rw [cz1, h1, hab] <;> simp
  unfold QPC
  rw [s1_lo u h1, hab]
  generalize σGen p (Gen.gate2 (n := 0) Gate.CZ) u = v at e0 e1 ⊢
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := fun hb => h0 (by rw [hab, hb]; rfl)
    rw [s1_lo v (by rw [e1]; rfl), e0, Aq_zero, ← Cz_val_one, lo_Mq_conj (inv_ne_zero hb)]
    exact Subgroup.pow_mem _ (CZh_mem_J 0) _
  · have hab0 : ((a, b) : ZMod p × ZMod p) ≠ 0 := fun h => ha (congrArg Prod.fst h)
    rw [s1_hi v (by rw [e1]; exact fun h => ha (congrArg Prod.snd h)), e0, e1, Aq_zero, bh_ne hab0]
    have hun : (hi p g (Hq p g ^ 2))⁻¹ * (hi p g (Mq p g a⁻¹))⁻¹ = hi p g (Mq p g (-a)) := by
      rw [← hi_inv, ← hi_inv, ← hi_mul, Hq_sq, Mq_neg_one_inv, Mq_inv (inv_ne_zero ha), inv_inv,
        Mq_mul neg_one_ne ha, neg_one_mul]
    have hmx : hi p g (Mq p g (-a)) * xh p g (-a) = xh p g 1 * hi p g (Mq p g (-a)) := by
      have h := hi_Mq_xh (p := p) (g := g) (neg_ne_zero.2 ha) (-a)
      rw [inv_mul_cancel₀ (neg_ne_zero.2 ha)] at h
      rw [← h]; group
    rw [alg_Ib (lo_hi_comm _ _) (loA_Cz ha) hun hmx]
    exact ιh_mem_J _

/-- A `Z` power on wire 1, `u` nonzero on wire 0. -/
theorem QPC_III {u : V p 2} (h0 : u 0 ≠ 0) (h1 : u 1 ≠ 0) (hc : (u 1).1 = 0) : QPC p g u := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ZMod p, u 0 = (a, b) := ⟨_, _, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ZMod p, u 1 = (0, d) := ⟨(u 1).2, Prod.ext hc rfl⟩
  have hd0 : d ≠ 0 := fun h => h1 (by rw [hd, h]; rfl)
  have hab0 : ((a, b) : ZMod p × ZMod p) ≠ 0 := fun h => h0 (by rw [hab, h])
  have e0 : σGen p (Gen.gate2 (n := 0) Gate.CZ) u 0 = (a, b) := by
    rw [cz0, hab, hd] <;> simp
  have e1 : σGen p (Gen.gate2 (n := 0) Gate.CZ) u 1 = (0, d + a) := by
    rw [cz1, hab, hd]
  unfold QPC
  rw [s1_hi u h1, hd, hab, Aq_zero, bh_ne hab0]
  generalize σGen p (Gen.gate2 (n := 0) Gate.CZ) u = v at e0 e1 ⊢
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := fun h => hab0 (by rw [h]; rfl)
    rw [add_zero] at e1
    rw [s1_hi v (by rw [e1]; exact fun h => hd0 (congrArg Prod.snd h)), e0, e1, bh_ne hab0, Aq_zero,
      Aq_zero, alg_conj3, ← Cz_val_one, hi_Mq_conj (inv_ne_zero hd0), lo_Mq_conj (inv_ne_zero hb), Hq_sq,
      hi_Mq_conj neg_one_ne, xh, Cz_pow_dgh, CX_val_conj_dgh]
    exact dgh_mem_J _ _ _
  · have hxy : xh p g (-a) * xh p g a = 1 := by rw [← xh_add, neg_add_cancel, xh_zero]
    by_cases hda : d + a = 0
    · have hd' : d = -a := eq_neg_of_add_eq_zero_left hda
      rw [hda] at e1
      rw [s1_lo v (by rw [e1]; rfl), e0]
      have hnu : hi p g (Mq p g d⁻¹) * hi p g (Hq p g ^ 2) = hi p g (Mq p g a⁻¹) := by
        rw [← hi_mul, Hq_sq, Mq_mul (inv_ne_zero hd0) neg_one_ne, hd', inv_neg, neg_mul_neg,
          mul_one]
      have hmx : hi p g (Mq p g a⁻¹) * xh p g 1 = xh p g a * hi p g (Mq p g a⁻¹) := by
        have h := hi_Mq_xh (p := p) (g := g) (inv_ne_zero ha) 1
        rw [inv_inv, mul_one] at h
        rw [← h]; group
      rw [alg_IIIb1 (lo_hi_comm _ _).symm (loA_Cz ha) hnu hmx hxy]
      exact ιh_mem_J _
    · have hγ : (0, d + a) ≠ (0 : ZMod p × ZMod p) := fun h => hda (congrArg Prod.snd h)
      rw [s1_hi v (by rw [e1]; exact hγ), e0, e1, Aq_zero]
      try rw [bh_ne hab0]
      have h1' : (hi p g (Hq p g ^ 2))⁻¹ * (hi p g (Mq p g (d + a)⁻¹))⁻¹ =
          hi p g (Mq p g (-(d + a))) := by
        rw [← hi_inv, ← hi_inv, ← hi_mul, Hq_sq, Mq_neg_one_inv, Mq_inv (inv_ne_zero hda), inv_inv,
          Mq_mul neg_one_ne hda, neg_one_mul]
      have h2' : hi p g (Mq p g d⁻¹) * hi p g (Hq p g ^ 2) = hi p g (Mq p g (-d⁻¹)) := by
        rw [← hi_mul, Hq_sq, Mq_mul (inv_ne_zero hd0) neg_one_ne, mul_neg_one]
      have h3' : hi p g (Mq p g (-(d + a))) * xh p g (-a) =
          xh p g ((-(d + a))⁻¹ * -a) * hi p g (Mq p g (-(d + a))) := by
        rw [← hi_Mq_xh (neg_ne_zero.2 hda) (-a)]; group
      have h4' : hi p g (Mq p g (-(d + a))) * hi p g (Mq p g (-d⁻¹)) =
          hi p g (Mq p g ((d + a) * d⁻¹)) := by
        rw [← hi_mul, Mq_mul (neg_ne_zero.2 hda) (neg_ne_zero.2 (inv_ne_zero hd0)), neg_mul_neg]
      have h5' : hi p g (Mq p g ((d + a) * d⁻¹)) * xh p g 1 =
          xh p g (((d + a) * d⁻¹)⁻¹ * 1) * hi p g (Mq p g ((d + a) * d⁻¹)) := by
        rw [← hi_Mq_xh (mul_ne_zero hda (inv_ne_zero hd0)) 1]; group
      have h6' : (xh p g 1)⁻¹ * xh p g ((-(d + a))⁻¹ * -a) * xh p g (((d + a) * d⁻¹)⁻¹ * 1) = 1 := by
        rw [← xh_neg, ← xh_add, ← xh_add]
        rw [show (-1 + (-(d + a))⁻¹ * -a + ((d + a) * d⁻¹)⁻¹ * 1 : ZMod p) = 0 by
          field_simp; ring, xh_zero]
      rw [alg_IIIb2 (lo_hi_comm _ _) (lo_hi_comm _ _).symm (loA_Cz ha) h1' h2' h3' h4' h5' h6']
      exact ιh_mem_J _

theorem P_dgh (x y : ZMod p) : lo p g (Sq p g x) * hi p g (Sq p g y) = dgh p g x y 0 := by
  rw [dgh, pow_val_zero, mul_one]

theorem D_dgh (x y : ZMod p) :
    (lo p g (Sq p g x))⁻¹ * (hi p g (Sq p g y))⁻¹ * Cz p g = dgh p g (-x) (-y) 1 := by
  rw [dgh, Sq_neg, Sq_neg, lo_inv, hi_inv, Cz_val_one]

/-- A rank-one diagonal is a conjugate of `S` on wire 0 by a power of `CX`. -/
theorem dgh_rank1 {a c : ZMod p} (ha : a ≠ 0) (hc : c ≠ 0) :
    dgh p g (-(c / a)) (-(a / c)) 1 =
      (xh p g (-(a / c)))⁻¹ * lo p g (Sq p g (-(c / a))) * xh p g (-(a / c)) := by
  calc dgh p g (-(c / a)) (-(a / c)) 1
      = dgh p g (-(c / a)) (0 + -(c / a) * (-(a / c)) ^ 2 + 2 * 0 * -(a / c))
          (0 + -(c / a) * -(a / c)) := by
        congr 1 <;> field_simp <;> ring
    _ = (CXh p g ^ (-(a / c)).val)⁻¹ * dgh p g (-(c / a)) 0 0 * CXh p g ^ (-(a / c)).val :=
        (CX_val_conj_dgh _ _ _ _).symm
    _ = (xh p g (-(a / c)))⁻¹ * lo p g (Sq p g (-(c / a))) * xh p g (-(a / c)) := by
        rw [lo_Sq_dgh]; rfl

/-- `X` powers on both wires. -/
theorem QPC_XX {u : V p 2} (ha' : (u 0).1 ≠ 0) (hc' : (u 1).1 ≠ 0) : QPC p g u := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ZMod p, u 0 = (a, b) := ⟨_, _, rfl⟩
  obtain ⟨c, d, hcd⟩ : ∃ c d : ZMod p, u 1 = (c, d) := ⟨_, _, rfl⟩
  have ha : a ≠ 0 := by rw [hab] at ha'; exact ha'
  have hc : c ≠ 0 := by rw [hcd] at hc'; exact hc'
  have hu1 : u 1 ≠ 0 := by rw [hcd]; exact fun h => hc (congrArg Prod.fst h)
  have hab0 : ((a, b) : ZMod p × ZMod p) ≠ 0 := fun h => ha (congrArg Prod.fst h)
  have habc0 : ((a, b + c) : ZMod p × ZMod p) ≠ 0 := fun h => ha (congrArg Prod.fst h)
  have e0 : σGen p (Gen.gate2 (n := 0) Gate.CZ) u 0 = (a, b + c) := by rw [cz0, hab, hcd]
  have e1 : σGen p (Gen.gate2 (n := 0) Gate.CZ) u 1 = (c, d + a) := by rw [cz1, hab, hcd]
  unfold QPC
  rw [s1_hi u hu1, hab, hcd]
  generalize σGen p (Gen.gate2 (n := 0) Gate.CZ) u = v at e0 e1 ⊢
  rw [s1_hi v (by rw [e1]; exact fun h => hc (congrArg Prod.fst h)), e0, e1, bh_ne habc0,
    bh_ne hab0, Aq_shift hc, Aq_shift ha, hi_mul, lo_mul, alg_XX_pre (lo_hi_comm _ _)]
  -- the box part
  have hT : lo p g (Hq p g ^ 3) * hi p g (Hq p g ^ 3) = (lo p g (Hq p g) * hi p g (Hq p g))⁻¹ := by
    rw [← Hq_inv, lo_inv, hi_inv, ← mul_inv_rev, lo_hi_comm]
  have hG0 : hi p g (qh p g 1 (Acirc p (c, d))) * lo p g (qh p g 1 (Acirc p (a, b))) =
      (lo p g (Sq p g (b / a)) * hi p g (Sq p g (d / c))) *
        (lo p g (Hq p g) * hi p g (Hq p g))⁻¹ * (lo p g (Mq p g a⁻¹) * hi p g (Mq p g c⁻¹)) := by
    rw [Aq_ne hc, Aq_ne ha, hi_mul, hi_mul, lo_mul, lo_mul,
      alg_prod3 (lo_hi_comm _ _).symm (lo_hi_comm _ _).symm (lo_hi_comm _ _).symm
        (lo_hi_comm _ _).symm (lo_hi_comm _ _).symm (lo_hi_comm _ _).symm, hT]
  rw [hG0]
  have hP : (lo p g (Sq p g (b / a)) * hi p g (Sq p g (d / c))) *
      ((lo p g (Sq p g (c / a)))⁻¹ * (hi p g (Sq p g (a / c)))⁻¹ * Cz p g) =
      ((lo p g (Sq p g (c / a)))⁻¹ * (hi p g (Sq p g (a / c)))⁻¹ * Cz p g) *
        (lo p g (Sq p g (b / a)) * hi p g (Sq p g (d / c))) := by
    rw [P_dgh, D_dgh, dgh_mul, dgh_mul]
    congr 1 <;> ring
  have hD : (lo p g (Sq p g (c / a)))⁻¹ * (hi p g (Sq p g (a / c)))⁻¹ * Cz p g =
      (xh p g (-(a / c)))⁻¹ * lo p g (Sq p g (-(c / a))) * xh p g (-(a / c)) := by
    rw [D_dgh]; exact dgh_rank1 ha hc
  have eL : lo p g (Mq p g a⁻¹) = (lo p g (Mq p g a))⁻¹ := by rw [← lo_inv, Mq_inv ha]
  have eH : hi p g (Mq p g c⁻¹) = (hi p g (Mq p g c))⁻¹ := by rw [← hi_inv, Mq_inv hc]
  have hN : ∀ X : Gh p g 2, (lo p g (Mq p g a⁻¹) * hi p g (Mq p g c⁻¹))⁻¹ * X *
      (lo p g (Mq p g a⁻¹) * hi p g (Mq p g c⁻¹)) =
      hi p g (Mq p g c) * (lo p g (Mq p g a) * X * (lo p g (Mq p g a))⁻¹) * (hi p g (Mq p g c))⁻¹ := by
    intro X; rw [eL, eH]; group
  have hkk : (lo p g (Mq p g a⁻¹) * hi p g (Mq p g c⁻¹))⁻¹ * yh p g (-(-(a / c))) *
      (lo p g (Mq p g a⁻¹) * hi p g (Mq p g c⁻¹)) = yh p g 1 := by
    rw [hN, lo_Mq_yh ha, hi_Mq_yh hc]
    congr 1
    field_simp
  set Y := Hq p g * Sq p g (-(c / a)) * (Hq p g)⁻¹ with hYdef
  have hLL : (lo p g (Mq p g a⁻¹) * hi p g (Mq p g c⁻¹))⁻¹ * lo p g Y *
      (lo p g (Mq p g a⁻¹) * hi p g (Mq p g c⁻¹)) = lo p g (Mq p g a * Y * (Mq p g a)⁻¹) := by
    rw [hN, ← lo_inv, ← lo_mul, ← lo_mul, ← lo_hi_comm, mul_inv_cancel_right]
  rw [alg_inner hP hD (HH_xh _) (HH_lo _) hkk hLL]
  -- the end: conjugating by `x⁻¹ y` is the swap
  have hxz : xh p g 1 * lo p g (Mq p g a * Y * (Mq p g a)⁻¹) =
      lo p g (Mq p g a * Y * (Mq p g a)⁻¹) * xh p g 1 := by
    have h1 : lo p g (Mq p g a) * xh p g a⁻¹ * (lo p g (Mq p g a))⁻¹ = xh p g 1 := by
      rw [lo_Mq_xh ha, mul_inv_cancel₀ ha]
    have h2 : lo p g (Mq p g a) * lo p g Y * (lo p g (Mq p g a))⁻¹ =
        lo p g (Mq p g a * Y * (Mq p g a)⁻¹) := by
      rw [← lo_inv, ← lo_mul, ← lo_mul]
    have := alg_comm_conj (m := lo p g (Mq p g a)) (x_comm_Y (p := p) (g := g) a⁻¹ (-(c / a)))
    rwa [h1, h2] at this
  have hu1' : (hi p g (Hq p g ^ 2))⁻¹ * (yh p g 1)⁻¹ * hi p g (Hq p g ^ 2) = yh p g 1 := by
    rw [← yh_neg, U_conj_yh, neg_neg]
  have hu2' : (hi p g (Hq p g ^ 2))⁻¹ * yh p g 1 * hi p g (Hq p g ^ 2) = (yh p g 1)⁻¹ := by
    rw [U_conj_yh, yh_neg]
  rw [alg_XX hu1' hu2' xy_SW hxz (lo_hi_comm _ _).symm (SW_lo _)]
  exact ιh_mem_J _

theorem QPC_all {u : V p 2} (hu : u ≠ 0) : QPC p g u := by
  by_cases h1 : u 1 = 0
  · exact QPC_I h1 (fun h0 => hu (V2_ext p h0 h1))
  · by_cases h0 : u 0 = 0
    · apply QPC_of_swap hu
      apply QPC_I (by rw [σSW]; exact h0) (by rw [σSW]; exact h1)
    · by_cases hc : (u 1).1 = 0
      · exact QPC_III h0 h1 hc
      · by_cases ha : (u 0).1 = 0
        · apply QPC_of_swap hu
          exact QPC_III (by rw [σSW]; exact h1) (by rw [σSW]; exact h0) (by rw [σSW]; exact ha)
        · exact QPC_XX ha hc

theorem lf2_cz (u : V p 2) (hu : u ≠ 0) :
    (s₁h p g 1 (σGen p (Gen.gate2 (n := 0) Gate.CZ) u))⁻¹ * CZh p g 0 * s₁h p g 1 u ∈ J p g 1 :=
  QPC_all hu

/-- The local facts on two wires. -/
theorem lf2 : LF2 p g where
  bS := lf2_bS
  bOne := lf2_bOne
  cz := lf2_cz
  czS0 := Cz_comm_loS
  heis := lf2_heis

end QCert.QuditClifford
