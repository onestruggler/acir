/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The local facts on three wires

`lf3 : LF3 p g`, from (C13)–(C15) and the facts on two wires.

On three wires, `L3 x` is a two-wire class on wires 0, 1, `U3 x` on wires
1, 2, and `V3 x = SWAP₁₂ L3 x SWAP₁₂` on wires 0, 2.  (C14) says that the
cycle `SWAP₀₁ SWAP₁₂` carries `L3` to `U3` (`cyc`), so that `V3 x` is also
`SWAP₀₁ U3 x SWAP₀₁` (`V3_eq`); (C15) says how `CX` from wire 2 to wire 1
conjugates `CZ₀₁`.  From these:

* `czcz`: (C15) conjugated by `S` on wire 1 gives `CZ₀₁ CZ₁₂ = CZ₁₂ CZ₀₁`;
* (C15) moved by the cycle: `CX₀₁ CZ₀₂ CX₀₁⁻¹ = CZ₁₂⁻¹ CZ₀₂`, and the
  Steinberg relation `CX₀₁⁻¹ CX₂₁ CX₀₁ = CX₂₀⁻¹ CX₂₁`;
* `bCZ`: the box on wires 0, 1 conjugates `CZ₁₂` to `CZ₀₂` or `CZ₁₂⁻¹`;
* `heis`: `c(Z^β ⊗ Z) = CZ₀₂ CZ₀₁^β`;
* `cz`: with `K = CX₂₀⁻¹` (which sends `Z` on wire 0 to `Z ⊗ I ⊗ Z`), the
  section of `(u₀, u₁, Z)` is the two-wire section of `(u₀, u₁)` followed
  by `K`, up to the stabiliser (`sec_K`); `K` conjugates the two-wire
  stabiliser into the three-wire one (`K_conj_J`), and the two-wire fact
  `lf2.cz` does the rest.

Every identity was checked on symplectic matrices for `p = 3, 5, 7` first.
-/
import QCert.QuditClifford.Width2

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-! ### Group identities -/

section Alg

variable {G : Type*} [Group G]

theorem alg_czcz {K X Y W Z s : G} (h15 : K * X = Y * X * K) (hsK : s * K * s⁻¹ = K)
    (hsY : s * Y * s⁻¹ = Y) (hsX : s * X * s⁻¹ = X * W * Z) (hKW : K * W = W * K) :
    K * Z = Z * K := by
  have h' : K * (X * W * Z) = Y * (X * W * Z) * K := by
    calc K * (X * W * Z) = (s * K * s⁻¹) * (s * X * s⁻¹) := by rw [hsK, hsX]
      _ = s * (K * X) * s⁻¹ := by group
      _ = s * (Y * X * K) * s⁻¹ := by rw [h15]
      _ = (s * Y * s⁻¹) * (s * X * s⁻¹) * (s * K * s⁻¹) := by group
      _ = Y * (X * W * Z) * K := by rw [hsY, hsX, hsK]
  have h2 : Y * X * (W * Z * K) = Y * X * (K * W * Z) := by
    calc Y * X * (W * Z * K) = Y * (X * W * Z) * K := by group
      _ = K * (X * W * Z) := h'.symm
      _ = (K * X) * W * Z := by group
      _ = Y * X * K * W * Z := by rw [h15]
      _ = Y * X * (K * W * Z) := by group
  have h3 := mul_left_cancel h2
  rw [hKW] at h3
  calc K * Z = W⁻¹ * (W * K * Z) := by group
    _ = W⁻¹ * (W * Z * K) := by rw [h3]
    _ = Z * K := by group

theorem alg_conj_back {u x y : G} (huu : u * u = 1) (h : u * x * u⁻¹ = y) : u⁻¹ * x * u = y := by
  calc u⁻¹ * x * u = (u * u)⁻¹ * (u * x * u⁻¹) * (u * u) := by group
    _ = y := by rw [huu, h]; group

theorem alg_comm_inv_conj {a b c : G} (h : a * b = b * a) :
    (c⁻¹ * a * c) * (c⁻¹ * b * c) = (c⁻¹ * b * c) * (c⁻¹ * a * c) := by
  calc (c⁻¹ * a * c) * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c := by group
    _ = c⁻¹ * (b * a) * c := by rw [h]
    _ = (c⁻¹ * b * c) * (c⁻¹ * a * c) := by group

theorem alg_conj_rule {K X Y T : G} (h : K * X = Y * X * K) :
    (T⁻¹ * K * T) * (T⁻¹ * X * T) = (T⁻¹ * Y * T) * (T⁻¹ * X * T) * (T⁻¹ * K * T) := by
  calc (T⁻¹ * K * T) * (T⁻¹ * X * T) = T⁻¹ * (K * X) * T := by group
    _ = T⁻¹ * (Y * X * K) * T := by rw [h]
    _ = _ := by group

/-- `K X = Y X K` gives `X K X⁻¹ = Y⁻¹ K`. -/
theorem alg_rule_conj {K X Y : G} (h : K * X = Y * X * K) : X * K * X⁻¹ = Y⁻¹ * K := by
  calc X * K * X⁻¹ = Y⁻¹ * (Y * X * K) * X⁻¹ := by group
    _ = Y⁻¹ * (K * X) * X⁻¹ := by rw [h]
    _ = Y⁻¹ * K := by group

/-- `K X = Y X K` with `K Y = Y K` gives `K⁻¹ X K = Y⁻¹ X`. -/
theorem alg_rule_conj' {K X Y : G} (h : K * X = Y * X * K) (hc : K * Y = Y * K) :
    K⁻¹ * X * K = Y⁻¹ * X := by
  calc K⁻¹ * X * K = K⁻¹ * Y⁻¹ * (Y * X * K) := by group
    _ = K⁻¹ * Y⁻¹ * (K * X) := by rw [h]
    _ = (Y * K)⁻¹ * (K * X) := by group
    _ = (K * Y)⁻¹ * (K * X) := by rw [hc]
    _ = Y⁻¹ * X := by group

theorem alg_cz {s s' t t' l l' K c : G} (ht : t = l * K) (ht' : t' = l' * K) :
    s'⁻¹ * c * s = (s'⁻¹ * t') * (K⁻¹ * (l'⁻¹ * c * l) * K) * (s⁻¹ * t)⁻¹ := by
  rw [ht, ht']; group

theorem alg_sconj {s a b : G} (hs : s * s = 1) : (s * a * s) * (s * b * s) = s * (a * b) * s := by
  calc (s * a * s) * (s * b * s) = s * a * (s * s) * b * s := by group
    _ = s * (a * b) * s := by rw [hs]; group

theorem alg_sinv {s a : G} (hs : s * s = 1) : (s * a * s)⁻¹ = s * a⁻¹ * s := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  rw [mul_inv_rev, mul_inv_rev, hs']; group

theorem alg_sconj_comm {s a b : G} (hs : s * s = 1) (h : a * b = b * a) :
    (s * a * s) * (s * b * s) = (s * b * s) * (s * a * s) := by
  rw [alg_sconj hs, alg_sconj hs, h]

theorem alg_steinberg {h L V U : G} (hc : h * U * h⁻¹ = U) (hK : L⁻¹ * U * L = V⁻¹ * U) :
    (h⁻¹ * L * h)⁻¹ * U * (h⁻¹ * L * h) = (h⁻¹ * V * h)⁻¹ * U := by
  have hc' : h⁻¹ * U * h = U := by
    calc h⁻¹ * U * h = h⁻¹ * (h * U * h⁻¹) * h := by rw [hc]
      _ = U := by group
  calc (h⁻¹ * L * h)⁻¹ * U * (h⁻¹ * L * h) = h⁻¹ * (L⁻¹ * (h * U * h⁻¹) * L) * h := by group
    _ = h⁻¹ * (V⁻¹ * U) * h := by rw [hc, hK]
    _ = (h⁻¹ * V * h)⁻¹ * (h⁻¹ * U * h) := by group
    _ = (h⁻¹ * V * h)⁻¹ * U := by rw [hc']

theorem alg_bCZ {a w X U : G} (hA : a⁻¹ * U * a = U) (hH : w⁻¹ * U * w = U⁻¹)
    (hX : X⁻¹ * U⁻¹ * X = U⁻¹) : (a * w * X)⁻¹ * U * (a * w * X) = U⁻¹ := by
  calc (a * w * X)⁻¹ * U * (a * w * X) = X⁻¹ * (w⁻¹ * (a⁻¹ * U * a) * w) * X := by group
    _ = U⁻¹ := by rw [hA, hH, hX]

theorem alg_ZZ {m w X K V : G} {n : ℕ} (hX : X * K * X⁻¹ = V⁻¹ * K) (hw1 : w * V * w⁻¹ = V⁻¹)
    (hw2 : w * K * w⁻¹ = K) (hm1 : m * V * m⁻¹ = V) (hm2 : m * K * m⁻¹ = K ^ n) :
    m * w * X * K * (m * w * X)⁻¹ = V * K ^ n := by
  have hw1' : w * V⁻¹ * w⁻¹ = V := by
    rw [show w * V⁻¹ * w⁻¹ = (w * V * w⁻¹)⁻¹ by group, hw1, inv_inv]
  calc m * w * X * K * (m * w * X)⁻¹ = m * (w * (X * K * X⁻¹) * w⁻¹) * m⁻¹ := by group
    _ = m * ((w * V⁻¹ * w⁻¹) * (w * K * w⁻¹)) * m⁻¹ := by rw [hX]; group
    _ = (m * V * m⁻¹) * (m * K * m⁻¹) := by rw [hw1', hw2]; group
    _ = V * K ^ n := by rw [hm1, hm2]

theorem alg_secK0 {S a0 w1 X01 X20 : G} (hS : S * S = 1) (hX20 : X20 = S * X01 * S)
    (hc : a0⁻¹ * S * a0 = S) (h2 : w1⁻¹ * X01⁻¹ * w1 = X01) :
    (S * (a0 * w1 * X01))⁻¹ * (a0 * X20⁻¹) = w1⁻¹ * S := by
  calc (S * (a0 * w1 * X01))⁻¹ * (a0 * X20⁻¹)
      = X01⁻¹ * w1⁻¹ * (a0⁻¹ * S * a0)⁻¹ * S⁻¹ * X01⁻¹ * S⁻¹ := by rw [hX20]; group
    _ = X01⁻¹ * w1⁻¹ * (S * S)⁻¹ * X01⁻¹ * S⁻¹ := by rw [hc]; group
    _ = X01⁻¹ * (w1⁻¹ * X01⁻¹ * w1) * w1⁻¹ * S⁻¹ := by rw [hS]; group
    _ = w1⁻¹ * S := by rw [h2, inv_eq_of_mul_eq_one_left hS]; group

theorem alg_secK1 {A w2 X21 T X20 : G} (h1 : T⁻¹ * X21 * T = X20) (h2 : T⁻¹ * w2 * T = w2)
    (hw : w2⁻¹ * X20⁻¹ * w2 = X20) : (A * w2 * X21 * T)⁻¹ * (A * T * X20⁻¹) = w2⁻¹ := by
  calc (A * w2 * X21 * T)⁻¹ * (A * T * X20⁻¹)
      = (T⁻¹ * X21 * T)⁻¹ * (T⁻¹ * w2 * T)⁻¹ * X20⁻¹ := by group
    _ = X20⁻¹ * (w2⁻¹ * X20⁻¹ * w2) * w2⁻¹ := by rw [h1, h2]; group
    _ = w2⁻¹ := by rw [hw]; group

theorem alg_secK2 {A a0 w1 w2 X01 X21 X20 : G} (hc1 : a0⁻¹ * X21 * a0 = X21)
    (hc2 : a0⁻¹ * w2 * a0 = w2) (hw : w1⁻¹ * X21⁻¹ * w1 = X21) (hw21 : w1⁻¹ * w2 * w1 = w2)
    (hw2X01 : X01⁻¹ * w2 * X01 = w2) (hst : X01⁻¹ * X21 * X01 = X20⁻¹ * X21)
    (hw20 : w2⁻¹ * X20⁻¹ * w2 = X20) (hcomm : X20⁻¹ * X21 * X20 = X21) :
    (A * w2 * X21 * (a0 * w1 * X01))⁻¹ * (A * (a0 * w1 * X01) * X20⁻¹) = X21 * w2⁻¹ := by
  calc (A * w2 * X21 * (a0 * w1 * X01))⁻¹ * (A * (a0 * w1 * X01) * X20⁻¹)
      = X01⁻¹ * (w1⁻¹ * ((a0⁻¹ * X21 * a0)⁻¹ * (a0⁻¹ * w2 * a0)⁻¹) * w1) * X01 * X20⁻¹ := by
        group
    _ = X01⁻¹ * ((w1⁻¹ * X21⁻¹ * w1) * (w1⁻¹ * w2 * w1)⁻¹) * X01 * X20⁻¹ := by
        rw [hc1, hc2]; group
    _ = (X01⁻¹ * X21 * X01) * (X01⁻¹ * w2 * X01)⁻¹ * X20⁻¹ := by rw [hw, hw21]; group
    _ = X20⁻¹ * X21 * (w2⁻¹ * X20⁻¹ * w2) * w2⁻¹ := by rw [hst, hw2X01]; group
    _ = X21 * w2⁻¹ := by rw [hw20, hcomm]

theorem alg_cz2 (s s' l l' X c : G) :
    s'⁻¹ * c * s = (s'⁻¹ * (l' * X⁻¹)) * (X * (l'⁻¹ * c * l) * X⁻¹) * (s⁻¹ * (l * X⁻¹))⁻¹ := by
  group

theorem alg_heis3 {X Y : G} (n : ℕ) (hc : X * Y = Y * X) :
    (Y * (X ^ n * X))⁻¹ * (X * (Y * X ^ n)) = 1 := by
  calc (Y * (X ^ n * X))⁻¹ * (X * (Y * X ^ n)) = X⁻¹ * (X ^ n)⁻¹ * Y⁻¹ * (X * Y) * X ^ n := by
        group
    _ = X⁻¹ * (X ^ n)⁻¹ * Y⁻¹ * (Y * X) * X ^ n := by rw [hc]
    _ = 1 := by group

end Alg

/-! ### Two-wire facts used here -/

theorem hH2_sq : hi p g (Hq p g ^ 2) * hi p g (Hq p g ^ 2) = 1 := by
  rw [← hi_mul, ← pow_add, show 2 + 2 = 4 from rfl, Hq_pow_four, hi_one]

theorem lH2_sq : lo p g (Hq p g ^ 2) * lo p g (Hq p g ^ 2) = 1 := by
  rw [← lo_mul, ← pow_add, show 2 + 2 = 4 from rfl, Hq_pow_four, lo_one]

/-- `H²` on wire 1 inverts `CX` (the control). -/
theorem hiH2_CXinv : (hi p g (Hq p g ^ 2))⁻¹ * (CXh p g)⁻¹ * hi p g (Hq p g ^ 2) = CXh p g := by
  have h := hi_Mq_conj_CX (p := p) (g := g) neg_one_ne
  rw [inv_neg, inv_one, CXh_val_neg, pow_val_one CXh_pow_p, ← Hq_sq] at h
  have h' : hi p g (Hq p g ^ 2) * (CXh p g)⁻¹ * (hi p g (Hq p g ^ 2))⁻¹ = CXh p g := by
    rw [show hi p g (Hq p g ^ 2) * (CXh p g)⁻¹ * (hi p g (Hq p g ^ 2))⁻¹ =
      (hi p g (Hq p g ^ 2) * CXh p g * (hi p g (Hq p g ^ 2))⁻¹)⁻¹ by group, h, inv_inv]
  exact alg_conj_back hH2_sq h'

/-- `H²` on wire 0 inverts `CX` (the target). -/
theorem loH2_CXinv : (lo p g (Hq p g ^ 2))⁻¹ * (CXh p g)⁻¹ * lo p g (Hq p g ^ 2) = CXh p g := by
  have h := lo_Mq_conj_CX (p := p) (g := g) neg_one_ne
  rw [CXh_val_neg, pow_val_one CXh_pow_p, ← Hq_sq] at h
  have h' : lo p g (Hq p g ^ 2) * (CXh p g)⁻¹ * (lo p g (Hq p g ^ 2))⁻¹ = CXh p g := by
    rw [show lo p g (Hq p g ^ 2) * (CXh p g)⁻¹ * (lo p g (Hq p g ^ 2))⁻¹ =
      (lo p g (Hq p g ^ 2) * CXh p g * (lo p g (Hq p g ^ 2))⁻¹)⁻¹ by group, h, inv_inv]
  exact alg_conj_back lH2_sq h'

theorem loH2_Cz' : (lo p g (Hq p g ^ 2))⁻¹ * Cz p g * lo p g (Hq p g ^ 2) = (Cz p g)⁻¹ :=
  alg_conj_back lH2_sq loH2_conj_Cz

/-- `S` on wire 0 past `CX`: (C12) rearranged. -/
theorem loS_CX : lo p g (qh p g 1 S) * CXh p g * (lo p g (qh p g 1 S))⁻¹ =
    CXh p g * hi p g (qh p g 1 S) * Cz p g := by
  have hc : lo p g (qh p g 1 S) * Cz p g * (lo p g (qh p g 1 S))⁻¹ = Cz p g := by
    rw [← Cz_comm_loS.eq, mul_inv_cancel_right]
  calc lo p g (qh p g 1 S) * CXh p g * (lo p g (qh p g 1 S))⁻¹
      = CXh p g * ((CXh p g)⁻¹ * lo p g (qh p g 1 S) * CXh p g) * (lo p g (qh p g 1 S))⁻¹ := by
        group
    _ = CXh p g * (hi p g (qh p g 1 S) * lo p g (qh p g 1 S) * Cz p g) *
          (lo p g (qh p g 1 S))⁻¹ := by rw [C12h]
    _ = CXh p g * hi p g (qh p g 1 S) * (lo p g (qh p g 1 S) * Cz p g * (lo p g (qh p g 1 S))⁻¹) := by
        group
    _ = CXh p g * hi p g (qh p g 1 S) * Cz p g := by rw [hc]

/-- `CX` conjugating `S` on wire 0 the other way. -/
theorem CX_loS : CXh p g * lo p g (qh p g 1 S) * (CXh p g)⁻¹ = dgh p g 1 1 (-1) := by
  have h := CX_val_conj_dgh (p := p) (g := g) (-1) 1 0 0
  rw [CXh_val_neg, pow_val_one CXh_pow_p, inv_inv, ← lo_Sq_dgh, Sq_one] at h
  rw [h]; congr 1 <;> ring

/-! ### Three wires -/

variable (p g) in
/-- Two-wire classes on wires 0, 1 of three. -/
noncomputable abbrev L3 : Gh p g 2 →* Gh p g 3 := padh 1 2

variable (p g) in
/-- Two-wire classes on wires 1, 2 of three. -/
noncomputable abbrev U3 : Gh p g 2 →* Gh p g 3 := ιh 2

variable (p g) in
/-- One-qudit classes on wire 0 of three. -/
noncomputable abbrev W0 : Gh p g 1 →* Gh p g 3 := padh 2 1

variable (p g) in
/-- One-qudit classes on wire 2 of three. -/
noncomputable abbrev W2 : Gh p g 1 →* Gh p g 3 := (ιh 2).comp (ιh 1)

theorem L3_lo (y : Gh p g 1) : L3 p g (lo p g y) = W0 p g y := padh_padh1 1 1 y

theorem L3_hi (y : Gh p g 1) : L3 p g (hi p g y) = U3 p g (lo p g y) := padh_ιh 1 1 y

theorem U3_hi (y : Gh p g 1) : U3 p g (hi p g y) = W2 p g y := rfl

theorem L3_W2 (x : Gh p g 2) (y : Gh p g 1) : L3 p g x * W2 p g y = W2 p g y * L3 p g x :=
  (commute_padh2_ιh2 (n := 1) x y).eq

theorem W0_U3 (y : Gh p g 1) (x : Gh p g 2) : W0 p g y * U3 p g x = U3 p g x * W0 p g y :=
  (commute_padh_ιh (n := 2) y x).eq

theorem W0_U3_conj (y : Gh p g 1) (x : Gh p g 2) : (W0 p g y)⁻¹ * U3 p g x * W0 p g y = U3 p g x :=
  conj_eq_of_commute_inv (commute_padh_ιh (n := 2) y x)

theorem SW_lo' (x : Gh p g 1) : SWh p g * lo p g x * SWh p g = hi p g x := by
  have h := SW_lo (p := p) (g := g) x
  rwa [SW_inv] at h

theorem SW_hi' (x : Gh p g 1) : SWh p g * hi p g x * SWh p g = lo p g x := by
  have h := SW_hi (p := p) (g := g) x
  rwa [SW_inv] at h

theorem pad_zero3 (w : Circ 3) : Circuit.pad 0 w = w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of y w ih =>
    rw [map_mul, ih]
    congr 1
    rcases y with c | c | c | c | y
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases y with c | c | c | _ | y
      · rfl
      · rfl
      · rfl
      · rcases y with c | c | _ | _ | y
        · rfl
        · rfl
        · rcases y with c | _ | _ | _ | _; rfl

theorem qh3_rule {w v : Circ 3} (h : Rule p g 3 w v) : qh p g 3 w = qh p g 3 v := by
  have := qh_rule (g := g) 0 h
  rwa [pad_zero3, pad_zero3] at this

theorem S01_sq : L3 p g (SWh p g) * L3 p g (SWh p g) = 1 := by rw [← map_mul, SW_sq, map_one]
theorem S12_sq : U3 p g (SWh p g) * U3 p g (SWh p g) = 1 := by rw [← map_mul, SW_sq, map_one]
theorem S01_inv : (L3 p g (SWh p g))⁻¹ = L3 p g (SWh p g) := by rw [← map_inv, SW_inv]
theorem S12_inv : (U3 p g (SWh p g))⁻¹ = U3 p g (SWh p g) := by rw [← map_inv, SW_inv]

/-- (C14): the cycle of the wires carries `CZ₀₁` to `CZ₁₂`. -/
theorem C14h : L3 p g (SWh p g) * U3 p g (SWh p g) * L3 p g (Cz p g) =
    U3 p g (Cz p g) * (L3 p g (SWh p g) * U3 p g (SWh p g)) := by
  have h := qh3_rule (g := g) Rule.C14
  simp only [seq_def, map_mul] at h
  have e1 : qh p g 3 (SWAP₁₂ p) = U3 p g (SWh p g) := rfl
  have e2 : qh p g 3 (SWAP₀₁ p) = L3 p g (SWh p g) := rfl
  have e3 : qh p g 3 CZ₀₁ = L3 p g (Cz p g) := rfl
  have e4 : qh p g 3 CZ₁₂ = U3 p g (Cz p g) := rfl
  rw [e1, e2, e3, e4] at h
  simpa only [mul_assoc] using h

/-- (C15). -/
theorem C15h : L3 p g (Cz p g) * U3 p g (CXh p g) =
    (L3 p g (SWh p g) * U3 p g (Cz p g) * L3 p g (SWh p g)) * U3 p g (CXh p g) * L3 p g (Cz p g) := by
  have h := qh3_rule (g := g) Rule.C15
  simp only [seq_def, map_mul, CZ₀₂] at h
  have e1 : qh p g 3 CX₂₁ = U3 p g (CXh p g) := rfl
  have e2 : qh p g 3 (SWAP₀₁ p) = L3 p g (SWh p g) := rfl
  have e3 : qh p g 3 CZ₀₁ = L3 p g (Cz p g) := rfl
  have e4 : qh p g 3 CZ₁₂ = U3 p g (Cz p g) := rfl
  rw [e1, e2, e3, e4] at h
  simpa only [mul_assoc] using h

/-- The cycle of the wires carries `L3` to `U3`. -/
theorem cyc (x : Gh p g 2) :
    L3 p g (SWh p g) * U3 p g (SWh p g) * L3 p g x * (L3 p g (SWh p g) * U3 p g (SWh p g))⁻¹ =
      U3 p g x := by
  set T := L3 p g (SWh p g) * U3 p g (SWh p g) with hT
  refine Gh.induction_on (P := fun x => T * L3 p g x * T⁻¹ = U3 p g x) x (by simp) ?_
  intro y x hx
  have hy : T * L3 p g (qh p g 2 (FreeMonoid.of y)) * T⁻¹ = U3 p g (qh p g 2 (FreeMonoid.of y)) := by
    rcases y with c | c | c | _ | y
    · rw [qh_gate0, map_one, map_one, mul_one, mul_inv_cancel]
    · have e : qh p g 2 (FreeMonoid.of (Gen.gate1 c)) = lo p g (qh p g 1 (Circuit.g1 c)) := rfl
      rw [e, L3_lo]
      have h1 : U3 p g (SWh p g) * W0 p g (qh p g 1 (Circuit.g1 c)) * (U3 p g (SWh p g))⁻¹ =
          W0 p g (qh p g 1 (Circuit.g1 c)) := by
        rw [← W0_U3, mul_inv_cancel_right]
      have h2 : L3 p g (SWh p g) * W0 p g (qh p g 1 (Circuit.g1 c)) * (L3 p g (SWh p g))⁻¹ =
          U3 p g (lo p g (qh p g 1 (Circuit.g1 c))) := by
        rw [← L3_lo, ← map_inv, ← map_mul, ← map_mul, SW_lo, L3_hi]
      calc T * W0 p g (qh p g 1 (Circuit.g1 c)) * T⁻¹
          = L3 p g (SWh p g) * (U3 p g (SWh p g) * W0 p g (qh p g 1 (Circuit.g1 c)) *
              (U3 p g (SWh p g))⁻¹) * (L3 p g (SWh p g))⁻¹ := by rw [hT]; group
        _ = _ := by rw [h1, h2]
    · cases c
      have e : qh p g 2 (FreeMonoid.of (Gen.gate2 (n := 0) Gate.CZ)) = Cz p g := rfl
      rw [e]
      have h := C14h (p := p) (g := g)
      rw [← mul_inv_eq_iff_eq_mul] at h
      exact h
    · rcases y with c | c | _ | _ | y
      · rw [qh_up, qh_gate0, map_one, map_one, map_one, mul_one, mul_inv_cancel]
      · have e : qh p g 2 (FreeMonoid.of (Gen.up (Gen.gate1 c))) = hi p g (qh p g 1 (Circuit.g1 c)) :=
          rfl
        rw [e, L3_hi]
        have h1 : U3 p g (SWh p g) * U3 p g (lo p g (qh p g 1 (Circuit.g1 c))) * (U3 p g (SWh p g))⁻¹ =
            W2 p g (qh p g 1 (Circuit.g1 c)) := by
          rw [← map_inv, ← map_mul, ← map_mul, SW_lo]; rfl
        have h2 : L3 p g (SWh p g) * W2 p g (qh p g 1 (Circuit.g1 c)) * (L3 p g (SWh p g))⁻¹ =
            W2 p g (qh p g 1 (Circuit.g1 c)) := by
          rw [L3_W2, mul_inv_cancel_right]
        calc T * U3 p g (lo p g (qh p g 1 (Circuit.g1 c))) * T⁻¹
            = L3 p g (SWh p g) * (U3 p g (SWh p g) * U3 p g (lo p g (qh p g 1 (Circuit.g1 c))) *
                (U3 p g (SWh p g))⁻¹) * (L3 p g (SWh p g))⁻¹ := by rw [hT]; group
          _ = _ := by rw [h1, h2, U3_hi]
      · rcases y with c | _ | _ | _ | _
        rw [qh_up, qh_up, qh_gate0, map_one, map_one, map_one, map_one, mul_one, mul_inv_cancel]
  rw [map_mul, map_mul, ← hx, ← hy]; group

theorem cyc' (x : Gh p g 2) :
    (L3 p g (SWh p g) * U3 p g (SWh p g))⁻¹ * U3 p g x * (L3 p g (SWh p g) * U3 p g (SWh p g)) =
      L3 p g x := by
  rw [← cyc x]; group

variable (p g) in
/-- Two-wire classes on wires 0, 2 of three. -/
noncomputable def V3 : Gh p g 2 →* Gh p g 3 :=
  (MulAut.conj (U3 p g (SWh p g))).toMonoidHom.comp (L3 p g)

theorem V3_apply (x : Gh p g 2) :
    V3 p g x = U3 p g (SWh p g) * L3 p g x * U3 p g (SWh p g) := by
  show U3 p g (SWh p g) * L3 p g x * (U3 p g (SWh p g))⁻¹ = _
  rw [S12_inv]

theorem V3_eq (x : Gh p g 2) :
    V3 p g x = L3 p g (SWh p g) * U3 p g x * L3 p g (SWh p g) := by
  rw [V3_apply, ← cyc x]
  calc U3 p g (SWh p g) * L3 p g x * U3 p g (SWh p g)
      = (L3 p g (SWh p g) * L3 p g (SWh p g)) * U3 p g (SWh p g) * L3 p g x *
          (U3 p g (SWh p g))⁻¹ := by
        rw [S01_sq, S12_inv]; group
    _ = _ := by group

theorem V3_lo (y : Gh p g 1) : V3 p g (lo p g y) = W0 p g y := by
  rw [V3_apply, L3_lo, ← W0_U3, mul_assoc, S12_sq, mul_one]

theorem V3_hi (y : Gh p g 1) : V3 p g (hi p g y) = W2 p g y := by
  rw [V3_apply, L3_hi, ← U3_hi, ← map_mul, ← map_mul, SW_lo']

/-- Wire 1 commutes with the classes on wires 0, 2. -/
theorem W1_V3 (y : Gh p g 1) (x : Gh p g 2) :
    U3 p g (lo p g y) * V3 p g x = V3 p g x * U3 p g (lo p g y) := by
  have e : U3 p g (lo p g y) = U3 p g (SWh p g) * W2 p g y * U3 p g (SWh p g) := by
    rw [← U3_hi, ← map_mul, ← map_mul, SW_hi']
  rw [V3_apply, e]
  exact alg_sconj_comm S12_sq (L3_W2 x y).symm

/-! ### `CZ₀₁` and `CZ₁₂` commute -/

theorem czcz' : L3 p g (Cz p g) * U3 p g (Cz p g) = U3 p g (Cz p g) * L3 p g (Cz p g) := by
  have hsK : U3 p g (lo p g (qh p g 1 S)) * L3 p g (Cz p g) * (U3 p g (lo p g (qh p g 1 S)))⁻¹ =
      L3 p g (Cz p g) := by
    rw [← L3_hi, ← map_inv, ← map_mul, ← map_mul, ← Cz_hiS, mul_inv_cancel_right]
  have hsY : U3 p g (lo p g (qh p g 1 S)) *
      (L3 p g (SWh p g) * U3 p g (Cz p g) * L3 p g (SWh p g)) * (U3 p g (lo p g (qh p g 1 S)))⁻¹ =
      L3 p g (SWh p g) * U3 p g (Cz p g) * L3 p g (SWh p g) := by
    rw [← V3_eq, W1_V3, mul_inv_cancel_right]
  have hsX : U3 p g (lo p g (qh p g 1 S)) * U3 p g (CXh p g) * (U3 p g (lo p g (qh p g 1 S)))⁻¹ =
      U3 p g (CXh p g) * W2 p g (qh p g 1 S) * U3 p g (Cz p g) := by
    rw [← map_inv, ← map_mul, ← map_mul, loS_CX, map_mul, map_mul, U3_hi]
  exact alg_czcz C15h hsK hsY hsX (L3_W2 _ _)

/-- `CZ₀₁` commutes with `CZ₀₂`. -/
theorem cz01_cz02 : L3 p g (Cz p g) * V3 p g (Cz p g) = V3 p g (Cz p g) * L3 p g (Cz p g) := by
  have h := alg_comm_inv_conj (c := L3 p g (SWh p g)) (czcz' (p := p) (g := g))
  have e1 : (L3 p g (SWh p g))⁻¹ * L3 p g (Cz p g) * L3 p g (SWh p g) = L3 p g (Cz p g) := by
    rw [← map_inv, ← map_mul, ← map_mul, SW_inv, SW_Cz.eq, mul_assoc, SW_sq, mul_one]
  have e2 : (L3 p g (SWh p g))⁻¹ * U3 p g (Cz p g) * L3 p g (SWh p g) = V3 p g (Cz p g) := by
    rw [S01_inv, ← V3_eq]
  rwa [e1, e2] at h

/-- `CZ₁₂` commutes with `CZ₀₂`. -/
theorem cz12_cz02 : U3 p g (Cz p g) * V3 p g (Cz p g) = V3 p g (Cz p g) * U3 p g (Cz p g) := by
  have h := alg_comm_inv_conj (c := U3 p g (SWh p g)) (czcz' (p := p) (g := g))
  have e1 : (U3 p g (SWh p g))⁻¹ * L3 p g (Cz p g) * U3 p g (SWh p g) = V3 p g (Cz p g) := by
    rw [S12_inv, ← V3_apply]
  have e2 : (U3 p g (SWh p g))⁻¹ * U3 p g (Cz p g) * U3 p g (SWh p g) = U3 p g (Cz p g) := by
    rw [← map_inv, ← map_mul, ← map_mul, SW_inv, SW_Cz.eq, mul_assoc, SW_sq, mul_one]
  rw [e1, e2] at h
  exact h.symm

/-! ### (C15) moved by the cycle, and the Steinberg relation -/

/-- `CX₀₁ CZ₀₂ CX₀₁⁻¹ = CZ₁₂⁻¹ CZ₀₂`. -/
theorem X01_K02 : L3 p g (CXh p g) * V3 p g (Cz p g) * (L3 p g (CXh p g))⁻¹ =
    (U3 p g (Cz p g))⁻¹ * V3 p g (Cz p g) := by
  set T := L3 p g (SWh p g) * U3 p g (SWh p g)
  have h := alg_conj_rule (T := T) (C15h (p := p) (g := g))
  have e1 : T⁻¹ * L3 p g (Cz p g) * T = V3 p g (Cz p g) := by
    rw [V3_apply, mul_inv_rev, S01_inv, S12_inv]
    calc U3 p g (SWh p g) * L3 p g (SWh p g) * L3 p g (Cz p g) * (L3 p g (SWh p g) * U3 p g (SWh p g))
        = U3 p g (SWh p g) * (L3 p g (SWh p g) * L3 p g (Cz p g) * (L3 p g (SWh p g))⁻¹) *
            U3 p g (SWh p g) := by rw [S01_inv]; group
      _ = _ := by rw [← map_inv, ← map_mul, ← map_mul, SW_Cz_conj]
  have e2 : T⁻¹ * U3 p g (CXh p g) * T = L3 p g (CXh p g) := cyc' _
  have e3 : T⁻¹ * (L3 p g (SWh p g) * U3 p g (Cz p g) * L3 p g (SWh p g)) * T = U3 p g (Cz p g) := by
    rw [mul_inv_rev, S01_inv, S12_inv]
    calc U3 p g (SWh p g) * L3 p g (SWh p g) * (L3 p g (SWh p g) * U3 p g (Cz p g) * L3 p g (SWh p g)) *
          (L3 p g (SWh p g) * U3 p g (SWh p g))
        = U3 p g (SWh p g) * (L3 p g (SWh p g) * L3 p g (SWh p g)) * U3 p g (Cz p g) *
            (L3 p g (SWh p g) * L3 p g (SWh p g)) * U3 p g (SWh p g) := by group
      _ = U3 p g (SWh p g) * U3 p g (Cz p g) * (U3 p g (SWh p g))⁻¹ := by
          rw [S01_sq, S12_inv]; group
      _ = _ := by rw [← map_inv, ← map_mul, ← map_mul, SW_Cz_conj]
  rw [e1, e2, e3] at h
  exact alg_rule_conj h

/-- The Steinberg relation `CX₀₁⁻¹ CX₂₁ CX₀₁ = CX₂₀⁻¹ CX₂₁`. -/
theorem steinberg : (L3 p g (CXh p g))⁻¹ * U3 p g (CXh p g) * L3 p g (CXh p g) =
    (V3 p g (CXh p g))⁻¹ * U3 p g (CXh p g) := by
  have hX01 : L3 p g (CXh p g) = (W0 p g (Hq p g))⁻¹ * L3 p g (Cz p g) * W0 p g (Hq p g) := by
    rw [CXh_eq, map_mul, map_mul, map_inv, L3_lo]
  have hX20 : V3 p g (CXh p g) = (W0 p g (Hq p g))⁻¹ * V3 p g (Cz p g) * W0 p g (Hq p g) := by
    rw [CXh_eq, map_mul, map_mul, map_inv, V3_lo]
  have hc : W0 p g (Hq p g) * U3 p g (CXh p g) * (W0 p g (Hq p g))⁻¹ = U3 p g (CXh p g) := by
    rw [W0_U3, mul_inv_cancel_right]
  have hK := alg_rule_conj' (C15h (p := p) (g := g)) (by rw [← V3_eq]; exact cz01_cz02)
  rw [← V3_eq] at hK
  rw [hX01, hX20]
  exact alg_steinberg hc hK

/-- `CX₂₀` and `CX₂₁` commute. -/
theorem X20_X21 : V3 p g (CXh p g) * U3 p g (CXh p g) = U3 p g (CXh p g) * V3 p g (CXh p g) := by
  set h0 := W0 p g (Hq p g)
  set h1 := U3 p g (lo p g (Hq p g))
  have hX21 : U3 p g (CXh p g) = h1⁻¹ * U3 p g (Cz p g) * h1 := by
    rw [CXh_eq, map_mul, map_mul, map_inv]
  have hX20 : V3 p g (CXh p g) = h0⁻¹ * V3 p g (Cz p g) * h0 := by
    rw [CXh_eq, map_mul, map_mul, map_inv, V3_lo]
  have step1 := alg_comm_inv_conj (c := h1) (cz12_cz02 (p := p) (g := g))
  have e1 : h1⁻¹ * V3 p g (Cz p g) * h1 = V3 p g (Cz p g) := by
    rw [mul_assoc, ← W1_V3, inv_mul_cancel_left]
  rw [e1, ← hX21] at step1
  have step2 := alg_comm_inv_conj (c := h0) step1
  have e2 : h0⁻¹ * U3 p g (CXh p g) * h0 = U3 p g (CXh p g) := by
    rw [mul_assoc, ← W0_U3, inv_mul_cancel_left]
  rw [e2, ← hX20] at step2
  exact step2.symm

/-- `CX₂₀ CZ₀₁ CX₂₀⁻¹ = CZ₁₂⁻¹ CZ₀₁`. -/
theorem X20_K01 : V3 p g (CXh p g) * L3 p g (Cz p g) * (V3 p g (CXh p g))⁻¹ =
    (U3 p g (Cz p g))⁻¹ * L3 p g (Cz p g) := by
  have hK12 : U3 p g (SWh p g) * U3 p g (Cz p g) * U3 p g (SWh p g) = U3 p g (Cz p g) := by
    rw [← map_mul, ← map_mul, ← Cz_SW]
  have hK02' : U3 p g (SWh p g) * V3 p g (Cz p g) * U3 p g (SWh p g) = L3 p g (Cz p g) := by
    rw [V3_apply]
    calc U3 p g (SWh p g) * (U3 p g (SWh p g) * L3 p g (Cz p g) * U3 p g (SWh p g)) * U3 p g (SWh p g)
        = (U3 p g (SWh p g) * U3 p g (SWh p g)) * L3 p g (Cz p g) *
            (U3 p g (SWh p g) * U3 p g (SWh p g)) := by group
      _ = _ := by rw [S12_sq]; group
  calc V3 p g (CXh p g) * L3 p g (Cz p g) * (V3 p g (CXh p g))⁻¹
      = (U3 p g (SWh p g) * L3 p g (CXh p g) * U3 p g (SWh p g)) *
          (U3 p g (SWh p g) * V3 p g (Cz p g) * U3 p g (SWh p g)) *
          (U3 p g (SWh p g) * L3 p g (CXh p g) * U3 p g (SWh p g))⁻¹ := by
        rw [hK02', ← V3_apply]
    _ = U3 p g (SWh p g) * (L3 p g (CXh p g) * V3 p g (Cz p g) * (L3 p g (CXh p g))⁻¹) *
          U3 p g (SWh p g) := by
        rw [alg_sinv S12_sq, alg_sconj S12_sq, alg_sconj S12_sq]
    _ = U3 p g (SWh p g) * ((U3 p g (Cz p g))⁻¹ * V3 p g (Cz p g)) * U3 p g (SWh p g) := by
        rw [X01_K02]
    _ = (U3 p g (SWh p g) * (U3 p g (Cz p g))⁻¹ * U3 p g (SWh p g)) *
          (U3 p g (SWh p g) * V3 p g (Cz p g) * U3 p g (SWh p g)) := by
        rw [alg_sconj S12_sq]
    _ = (U3 p g (Cz p g))⁻¹ * L3 p g (Cz p g) := by
        rw [hK02', ← alg_sinv S12_sq, hK12]

/-! ### Membership -/

theorem K01_mem : L3 p g (Cz p g) ∈ J p g 2 := CZh_mem_J 1

theorem U3_mem (x : Gh p g 2) : U3 p g x ∈ J p g 2 := ιh_mem_J x

theorem V3_Cz_mem : V3 p g (Cz p g) ∈ J p g 2 := by
  rw [V3_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (U3_mem _) K01_mem) (U3_mem _)

theorem W2_mem (y : Gh p g 1) : W2 p g y ∈ J p g 2 := by
  rw [← U3_hi]; exact U3_mem _

theorem W0_Sq_mem (c : ZMod p) : W0 p g (Sq p g c) ∈ J p g 2 := by
  rw [Sq, map_pow]
  exact Subgroup.pow_mem _ (S0h_mem_J 2) _

/-! ### The local facts -/

theorem lf3_czcz : Commute (CZh p g 1) (ιh 2 (CZh p g 0)) := czcz'

theorem lf3_bCZ (u : ZMod p × ZMod p) :
    (padh 1 2 (bh p g u))⁻¹ * ιh 2 (CZh p g 0) * padh 1 2 (bh p g u) ∈ J p g 2 := by
  show (L3 p g (bh p g u))⁻¹ * U3 p g (Cz p g) * L3 p g (bh p g u) ∈ J p g 2
  by_cases hu : u = 0
  · subst hu
    rw [bh_zero, S01_inv, ← V3_eq]
    exact V3_Cz_mem
  · rw [bh_ne hu, map_mul, map_mul, L3_lo, L3_hi, xh_one]
    have hA : (W0 p g (qh p g 1 (Acirc p u)))⁻¹ * U3 p g (Cz p g) * W0 p g (qh p g 1 (Acirc p u)) =
        U3 p g (Cz p g) := W0_U3_conj _ _
    have hH : (U3 p g (lo p g (Hq p g ^ 2)))⁻¹ * U3 p g (Cz p g) * U3 p g (lo p g (Hq p g ^ 2)) =
        (U3 p g (Cz p g))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, loH2_Cz', map_inv]
    have hc : Commute (L3 p g (CXh p g)) (U3 p g (Cz p g)) := by
      have h0 : Commute (W0 p g (Hq p g)) (U3 p g (Cz p g)) := commute_padh_ιh (n := 2) _ _
      have hL : Commute (L3 p g (Cz p g)) (U3 p g (Cz p g)) := czcz'
      rw [CXh_eq, map_mul, map_mul, map_inv, L3_lo]
      exact (h0.inv_left.mul_left hL).mul_left h0
    have hX : (L3 p g (CXh p g))⁻¹ * (U3 p g (Cz p g))⁻¹ * L3 p g (CXh p g) =
        (U3 p g (Cz p g))⁻¹ := conj_eq_of_commute_inv hc.inv_right
    rw [alg_bCZ hA hH hX]
    exact Subgroup.inv_mem _ (U3_mem _)

/-- `c(Z^β ⊗ Z) = CZ₀₂ CZ₀₁^β`. -/
theorem cP_ZZ (β : ZMod p) : cP p g 1 (Fin.cons (0, β) (eZ p 0)) =
    V3 p g (Cz p g) * L3 p g (Cz p g) ^ β.val := by
  have h1 : (Fin.cons (0, β) (eZ p 0) : V p 2) 1 ≠ 0 := fun h => by
    have : ((0, 1) : ZMod p × ZMod p).2 = (0 : ZMod p × ZMod p).2 := congrArg Prod.snd h
    exact one_ne_zero this
  have hP : (Fin.cons (0, β) (eZ p 0) : V p 2) ≠ 0 := fun h => h1 (congrFun h 1)
  have hs : s₁h p g 1 (Fin.cons (0, β) (eZ p 0)) = bh p g (0, β) := by
    rw [s1_hi _ h1]
    show hi p g (qh p g 1 (Acirc p (0, 1))) * bh p g (0, β) = _
    rw [Aq_zero, inv_one, Mq_one, map_one, one_mul]
  unfold cP
  rw [if_neg hP, hs]
  show U3 p g (bh p g (0, β)) * L3 p g (Cz p g) * (U3 p g (bh p g (0, β)))⁻¹ = _
  by_cases hβ : β = 0
  · subst hβ
    rw [show ((0 : ZMod p), (0 : ZMod p)) = 0 from rfl, bh_zero, S12_inv, ← V3_apply,
      ZMod.val_zero, pow_zero, mul_one]
  · have hβ0 : ((0 : ZMod p), β) ≠ 0 := fun h => hβ (congrArg Prod.snd h)
    rw [bh_ne hβ0, Aq_zero, xh_one, map_mul, map_mul, U3_hi]
    have hX : U3 p g (CXh p g) * L3 p g (Cz p g) * (U3 p g (CXh p g))⁻¹ =
        (V3 p g (Cz p g))⁻¹ * L3 p g (Cz p g) := by
      have := alg_rule_conj (C15h (p := p) (g := g))
      rwa [← V3_eq] at this
    have hw1 : W2 p g (Hq p g ^ 2) * V3 p g (Cz p g) * (W2 p g (Hq p g ^ 2))⁻¹ =
        (V3 p g (Cz p g))⁻¹ := by
      rw [← V3_hi, ← map_inv, ← map_mul, ← map_mul, hiH2_conj_Cz, map_inv]
    have hw2 : W2 p g (Hq p g ^ 2) * L3 p g (Cz p g) * (W2 p g (Hq p g ^ 2))⁻¹ = L3 p g (Cz p g) := by
      rw [← L3_W2, mul_inv_cancel_right]
    have hm1 : U3 p g (lo p g (Mq p g β⁻¹)) * V3 p g (Cz p g) * (U3 p g (lo p g (Mq p g β⁻¹)))⁻¹ =
        V3 p g (Cz p g) := by
      rw [W1_V3, mul_inv_cancel_right]
    have hm2 : U3 p g (lo p g (Mq p g β⁻¹)) * L3 p g (Cz p g) * (U3 p g (lo p g (Mq p g β⁻¹)))⁻¹ =
        L3 p g (Cz p g) ^ β.val := by
      have := hi_Mq_conj' (p := p) (g := g) (inv_ne_zero hβ) 1
      rw [Cz_val_one, one_mul, inv_inv] at this
      rw [← L3_hi, ← map_inv, ← map_mul, ← map_mul, this, map_pow]
    exact alg_ZZ hX hw1 hw2 hm1 hm2

theorem lf3_heis (β : ZMod p) : (cP p g 1 (Fin.cons (0, β + 1) (eZ p 0)))⁻¹ *
    (CZh p g 1 * cP p g 1 (Fin.cons (0, β) (eZ p 0))) ∈ Kst p g 2 := by
  rw [cP_ZZ, cP_ZZ]
  show (V3 p g (Cz p g) * L3 p g (Cz p g) ^ (β + 1).val)⁻¹ *
    (L3 p g (Cz p g) * (V3 p g (Cz p g) * L3 p g (Cz p g) ^ β.val)) ∈ Kst p g 2
  rw [← map_pow, ← map_pow, Cz_val_add, Cz_val_one, map_mul, map_pow,
    alg_heis3 _ cz01_cz02]
  exact Subgroup.one_mem _

/-! ### `CZ₀₁` on the sections -/

theorem s3_eq (a b : ZMod p × ZMod p) :
    s₁h p g 2 (Fin.cons a (Fin.cons b (eZ p 0))) = U3 p g (bh p g b) * L3 p g (bh p g a) := by
  have hz : Fin.tail (Fin.cons b (eZ p 0) : V p 2) ≠ 0 := by
    rw [Fin.tail_cons]; exact eZ_ne_zero 0
  have hz' : Fin.tail (Fin.cons a (Fin.cons b (eZ p 0)) : V p 3) ≠ 0 := by
    rw [Fin.tail_cons]; intro h; exact hz (by rw [h]; rfl)
  have hA : qh p g 1 (Acirc p ((Fin.cons b (eZ p 0) : V p 2) 1)) = 1 := by
    show qh p g 1 (Acirc p (0, 1)) = 1
    rw [Aq_zero, inv_one, Mq_one]
  rw [s₁h_succ 1 _ hz', Fin.tail_cons, s₁h_one _ hz, hA, map_one, one_mul, Fin.cons_zero,
    Fin.cons_zero]

theorem σ3_eq (a b : ZMod p × ZMod p) :
    σGen p (Gen.gate2 (n := 1) Gate.CZ) (Fin.cons a (Fin.cons b (eZ p 0))) =
      Fin.cons (a.1, a.2 + b.1) (Fin.cons (b.1, b.2 + a.1) (eZ p 0)) := by
  rw [σGen_CZ]; rfl

theorem σ2_eq (a b : ZMod p × ZMod p) :
    σGen p (Gen.gate2 (n := 0) Gate.CZ) ![a, b] = ![(a.1, a.2 + b.1), (b.1, b.2 + a.1)] :=
  V2_ext p (cz0 _) (cz1 _)

/-- `CX₂₀` conjugates the two-wire stabiliser into the three-wire one. -/
theorem K_conj_J {j : Gh p g 2} (hj : j ∈ J p g 1) :
    V3 p g (CXh p g) * L3 p g j * (V3 p g (CXh p g))⁻¹ ∈ J p g 2 := by
  let f : Gh p g 2 →* Gh p g 3 := (MulAut.conj (V3 p g (CXh p g))).toMonoidHom.comp (L3 p g)
  have hf : ∀ z, f z = V3 p g (CXh p g) * L3 p g z * (V3 p g (CXh p g))⁻¹ := fun _ => rfl
  rw [← hf]
  refine (Subgroup.closure_le ((J p g 2).comap f)).2 ?_ hj
  rintro _ (⟨z, rfl⟩ | h | h)
  · rw [SetLike.mem_coe, Subgroup.mem_comap, hf, L3_hi, ← W1_V3, mul_inv_cancel_right]
    exact U3_mem _
  · subst h
    rw [SetLike.mem_coe, Subgroup.mem_comap, hf, show S0h p g 1 = lo p g (qh p g 1 S) from rfl,
      L3_lo, ← V3_lo, ← map_inv, ← map_mul, ← map_mul, CX_loS, dgh, map_mul, map_mul, map_pow,
      V3_lo, V3_hi]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (W0_Sq_mem _) (W2_mem _))
      (Subgroup.pow_mem _ V3_Cz_mem _)
  · rw [Set.mem_singleton_iff] at h; subst h
    rw [SetLike.mem_coe, Subgroup.mem_comap, hf]
    show V3 p g (CXh p g) * L3 p g (Cz p g) * (V3 p g (CXh p g))⁻¹ ∈ J p g 2
    rw [X20_K01]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (U3_mem _)) K01_mem

/-- The section of `(a, b, Z)` is the two-wire section of `(a, b)` followed
by `CX₂₀⁻¹`, up to the stabiliser. -/
theorem sec_K {a b : ZMod p × ZMod p} (hab : ¬(a = 0 ∧ b = 0)) :
    (U3 p g (bh p g b) * L3 p g (bh p g a))⁻¹ * (L3 p g (s₁h p g 1 ![a, b]) *
      (V3 p g (CXh p g))⁻¹) ∈ J p g 2 := by
  have hw20 : (W2 p g (Hq p g ^ 2))⁻¹ * (V3 p g (CXh p g))⁻¹ * W2 p g (Hq p g ^ 2) =
      V3 p g (CXh p g) := by
    have := congrArg (V3 p g) (hiH2_CXinv (p := p) (g := g))
    simpa only [map_mul, map_inv, V3_hi] using this
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := fun h => hab ⟨h, rfl⟩
    rw [s1_lo ![a, 0] rfl, show (![a, 0] : V p 2) 0 = a from rfl, bh_zero, bh_ne ha, map_mul,
      map_mul, L3_lo, L3_hi, xh_one]
    have hc : (W0 p g (qh p g 1 (Acirc p a)))⁻¹ * U3 p g (SWh p g) * W0 p g (qh p g 1 (Acirc p a)) =
        U3 p g (SWh p g) := W0_U3_conj _ _
    have h2 : (U3 p g (lo p g (Hq p g ^ 2)))⁻¹ * (L3 p g (CXh p g))⁻¹ * U3 p g (lo p g (Hq p g ^ 2)) =
        L3 p g (CXh p g) := by
      have := congrArg (L3 p g) (hiH2_CXinv (p := p) (g := g))
      simpa only [map_mul, map_inv, L3_hi] using this
    rw [alg_secK0 S12_sq (V3_apply _) hc h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (U3_mem _)) (U3_mem _)
  · have hb' : (![a, b] : V p 2) 1 ≠ 0 := hb
    rw [s1_hi ![a, b] hb', show (![a, b] : V p 2) 1 = b from rfl,
      show (![a, b] : V p 2) 0 = a from rfl, bh_ne hb, map_mul, map_mul, map_mul, L3_hi, U3_hi,
      xh_one]
    by_cases ha : a = 0
    · subst ha
      rw [bh_zero]
      have h1 : (L3 p g (SWh p g))⁻¹ * U3 p g (CXh p g) * L3 p g (SWh p g) = V3 p g (CXh p g) := by
        rw [S01_inv, ← V3_eq]
      have h2 : (L3 p g (SWh p g))⁻¹ * W2 p g (Hq p g ^ 2) * L3 p g (SWh p g) =
          W2 p g (Hq p g ^ 2) := conj_eq_of_commute_inv (L3_W2 _ _)
      rw [alg_secK1 h1 h2 hw20]
      exact Subgroup.inv_mem _ (W2_mem _)
    · rw [bh_ne ha, map_mul, map_mul, L3_lo, L3_hi, xh_one]
      have hc1 : (W0 p g (qh p g 1 (Acirc p a)))⁻¹ * U3 p g (CXh p g) *
          W0 p g (qh p g 1 (Acirc p a)) = U3 p g (CXh p g) := W0_U3_conj _ _
      have hc2 : (W0 p g (qh p g 1 (Acirc p a)))⁻¹ * W2 p g (Hq p g ^ 2) *
          W0 p g (qh p g 1 (Acirc p a)) = W2 p g (Hq p g ^ 2) := by
        rw [← U3_hi]; exact W0_U3_conj _ _
      have hw : (U3 p g (lo p g (Hq p g ^ 2)))⁻¹ * (U3 p g (CXh p g))⁻¹ *
          U3 p g (lo p g (Hq p g ^ 2)) = U3 p g (CXh p g) := by
        have := congrArg (U3 p g) (loH2_CXinv (p := p) (g := g))
        simpa only [map_mul, map_inv] using this
      have hw21 : (U3 p g (lo p g (Hq p g ^ 2)))⁻¹ * W2 p g (Hq p g ^ 2) *
          U3 p g (lo p g (Hq p g ^ 2)) = W2 p g (Hq p g ^ 2) := by
        rw [← U3_hi]
        exact conj_eq_of_commute_inv
          (Commute.map (show Commute (lo p g (Hq p g ^ 2)) (hi p g (Hq p g ^ 2)) from
            lo_hi_comm _ _) (U3 p g))
      have hw2X01 : (L3 p g (CXh p g))⁻¹ * W2 p g (Hq p g ^ 2) * L3 p g (CXh p g) =
          W2 p g (Hq p g ^ 2) := conj_eq_of_commute_inv (L3_W2 _ _)
      have hcomm : (V3 p g (CXh p g))⁻¹ * U3 p g (CXh p g) * V3 p g (CXh p g) = U3 p g (CXh p g) :=
        conj_eq_of_commute_inv X20_X21
      rw [alg_secK2 hc1 hc2 hw hw21 hw2X01 steinberg hw20 hcomm]
      exact Subgroup.mul_mem _ (U3_mem _) (Subgroup.inv_mem _ (W2_mem _))

theorem lf3_cz (u0 u1 : ZMod p × ZMod p) :
    (s₁h p g 2 (σGen p (Gen.gate2 (n := 1) Gate.CZ) (Fin.cons u0 (Fin.cons u1 (eZ p 0)))))⁻¹ *
      CZh p g 1 * s₁h p g 2 (Fin.cons u0 (Fin.cons u1 (eZ p 0))) ∈ J p g 2 := by
  rw [σ3_eq, s3_eq, s3_eq]
  show (U3 p g (bh p g (u1.1, u1.2 + u0.1)) * L3 p g (bh p g (u0.1, u0.2 + u1.1)))⁻¹ *
    L3 p g (Cz p g) * (U3 p g (bh p g u1) * L3 p g (bh p g u0)) ∈ J p g 2
  by_cases h0 : u0 = 0 ∧ u1 = 0
  · obtain ⟨rfl, rfl⟩ := h0
    have e1 : ((0 : ZMod p × ZMod p).1, (0 : ZMod p × ZMod p).2 + (0 : ZMod p × ZMod p).1) = 0 := by
      ext <;> simp
    rw [e1, bh_zero]
    have e : (U3 p g (SWh p g) * L3 p g (SWh p g))⁻¹ * L3 p g (Cz p g) *
        (U3 p g (SWh p g) * L3 p g (SWh p g)) = U3 p g (Cz p g) := by
      calc (U3 p g (SWh p g) * L3 p g (SWh p g))⁻¹ * L3 p g (Cz p g) *
            (U3 p g (SWh p g) * L3 p g (SWh p g))
          = (L3 p g (SWh p g))⁻¹ * ((U3 p g (SWh p g))⁻¹ * L3 p g (Cz p g) * U3 p g (SWh p g)) *
              L3 p g (SWh p g) := by group
        _ = (L3 p g (SWh p g))⁻¹ * V3 p g (Cz p g) * L3 p g (SWh p g) := by
            rw [S12_inv, ← V3_apply]
        _ = (L3 p g (SWh p g))⁻¹ * (L3 p g (SWh p g) * U3 p g (Cz p g) * L3 p g (SWh p g)) *
              L3 p g (SWh p g) := by rw [V3_eq]
        _ = U3 p g (Cz p g) * (L3 p g (SWh p g) * L3 p g (SWh p g)) := by group
        _ = U3 p g (Cz p g) := by rw [S01_sq, mul_one]
    rw [e]
    exact U3_mem _
  · have hv : (![u0, u1] : V p 2) ≠ 0 := fun h => h0 ⟨congrFun h 0, congrFun h 1⟩
    have h0' : ¬((u0.1, u0.2 + u1.1) = (0 : ZMod p × ZMod p) ∧
        (u1.1, u1.2 + u0.1) = (0 : ZMod p × ZMod p)) := by
      rintro ⟨ha, hb⟩
      apply h0
      have e1 : u0.1 = 0 := congrArg Prod.fst ha
      have e2 : u1.1 = 0 := congrArg Prod.fst hb
      have e3 : u0.2 + u1.1 = 0 := congrArg Prod.snd ha
      have e4 : u1.2 + u0.1 = 0 := congrArg Prod.snd hb
      rw [e2, add_zero] at e3
      rw [e1, add_zero] at e4
      exact ⟨Prod.ext e1 e3, Prod.ext e2 e4⟩
    have hB2 := lf2_cz (p := p) (g := g) ![u0, u1] hv
    rw [σ2_eq] at hB2
    have hK : V3 p g (CXh p g) * ((L3 p g (s₁h p g 1 ![(u0.1, u0.2 + u1.1), (u1.1, u1.2 + u0.1)]))⁻¹ *
        L3 p g (Cz p g) * L3 p g (s₁h p g 1 ![u0, u1])) * (V3 p g (CXh p g))⁻¹ ∈ J p g 2 := by
      have := K_conj_J hB2
      simpa only [map_mul, map_inv] using this
    rw [alg_cz2 (U3 p g (bh p g u1) * L3 p g (bh p g u0))
      (U3 p g (bh p g (u1.1, u1.2 + u0.1)) * L3 p g (bh p g (u0.1, u0.2 + u1.1)))
      (L3 p g (s₁h p g 1 ![u0, u1]))
      (L3 p g (s₁h p g 1 ![(u0.1, u0.2 + u1.1), (u1.1, u1.2 + u0.1)])) (V3 p g (CXh p g))
      (L3 p g (Cz p g))]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (sec_K h0') hK) (Subgroup.inv_mem _ (sec_K h0))

/-- The local facts on three wires. -/
theorem lf3 : LF3 p g where
  bCZ := lf3_bCZ
  cz := lf3_cz
  czcz := lf3_czcz
  heis := lf3_heis

end QCert.QuditClifford
