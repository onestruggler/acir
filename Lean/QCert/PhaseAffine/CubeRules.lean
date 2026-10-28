/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Rules (35), (37), (38), (40), (42) on the classes of `T`-atoms

`CS` and `CCZ` (Definitions 17, 18 of Blake, arXiv:2603.06466) are products
of atoms: `CS` is `T` on `x₀ + x₁` and on `x₀ - x₁` (to the powers `±1/2`)
and `T⁻¹` on `x₁`, times quadratic diagonals (`csQ_dec`); `CCZ` is the
third difference of `T` on `x₀, x₁, x₂` (`cczQ_dec`).  So, modulo the
quadratic diagonal group and conjugated by a linear circuit `Y` with rows
`r₀, r₁, r₂`, `CS` is `cs r₁ r₀` and `CCZ` is `ccz r₀ r₁ r₂`, and the rules
become relations among the classes `tau u`:

* (37): `cs (x r₁) r₀ = x cs r₁ r₀`; (35): `cs r₁ (a r₀) = a² cs r₁ r₀`;
* (42): `cs (r₁ + r₂) r₀ = cs r₁ r₀ + cs r₂ r₀`;
* (38): `cs r₂ (r₀ + r₁) = cs r₂ r₀ + cs r₂ r₁ + ccz r₀ r₁ r₂`;
* (40): `ccz r₀ r₁ (x r₂) = x ccz r₀ r₁ r₂`.
-/
import QCert.PhaseAffine.CubeV

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ} [Fact d.Prime]

local notation "𝒢" => gateData d lv

/-! ### Forms -/

theorem fsum_single {n : ℕ} (i : Fin n) (c : ZMod d) (y : Lab d n) :
    ∑ j, (Pi.single i c : Lab d n) j * y j = c * y i := by
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul]) (by simp),
    Pi.single_eq_same]

theorem fsum_add {n : ℕ} (u v y : Lab d n) :
    ∑ j, (u + v) j * y j = ∑ j, u j * y j + ∑ j, v j * y j := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem fsum_cons {n : ℕ} (a b : ZMod d) (u y : Lab d n) :
    ∑ j, (Fin.cons a u : Lab d (n + 1)) j * (Fin.cons b y : Lab d (n + 1)) j =
      a * b + ∑ j, u j * y j := by
  rw [Fin.sum_univ_succ]; rfl

theorem cons_single {n : ℕ} (i : Fin n) (c : ZMod d) :
    (Fin.cons 0 (Pi.single i c) : Lab d (n + 1)) = Pi.single i.succ c := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [(Fin.succ_ne_zero i).symm]
  · simp [Pi.single_apply, Fin.succ_inj]

theorem cons_zero_add {n : ℕ} (u v : Lab d n) :
    (Fin.cons 0 (u + v) : Lab d (n + 1)) = Fin.cons 0 u + Fin.cons 0 v := by
  funext j; refine Fin.cases (by simp) (fun k => by simp) j

theorem cons_zero_sub {n : ℕ} (u v : Lab d n) :
    (Fin.cons 0 (u - v) : Lab d (n + 1)) = Fin.cons 0 u - Fin.cons 0 v := by
  funext j; refine Fin.cases (by simp) (fun k => by simp) j

theorem cons_zero_smul {n : ℕ} (c : ZMod d) (u : Lab d n) :
    (Fin.cons 0 (c • u) : Lab d (n + 1)) = c • Fin.cons 0 u := by
  funext j; refine Fin.cases (by simp) (fun k => by simp) j

/-! ### Rows of the generators -/

theorem pb_shift_zero {n : ℕ} (W : C d lv n) (hW : IsLinW W) :
    pb (Pi.single 0 1 : Lab d (n + 1)) (shift W) = Pi.single 0 1 := by
  refine pb_eq_of _ (isLinW_shift hW) _ _ fun y => ?_
  rw [fsum_single, fsum_single, ← Fin.cons_self_tail y, sem_f_shift]; rfl

theorem pb_shift_cons {n : ℕ} (W : C d lv n) (hW : IsLinW W) (u : Lab d n) :
    pb (Fin.cons 0 u : Lab d (n + 1)) (shift W) = Fin.cons 0 (pb u W) := by
  refine pb_eq_of _ (isLinW_shift hW) _ _ fun y => ?_
  rw [← Fin.cons_self_tail y, sem_f_shift, fsum_cons, fsum_cons, sem_pb_apply W hW]

theorem pb_shift_single {n : ℕ} (W : C d lv n) (hW : IsLinW W) (i : Fin n) :
    pb (Pi.single i.succ 1 : Lab d (n + 1)) (shift W) = Fin.cons 0 (pb (Pi.single i 1) W) := by
  rw [← cons_single, pb_shift_cons W hW]

theorem pb_M_zero {n : ℕ} (x : (ZMod d)ˣ) :
    pb (Pi.single 0 1 : Lab d (n + 1)) (g1 (Gate.M (lv := lv) x)) = Pi.single 0 (x : ZMod d) := by
  refine pb_eq_of _ (isLinW_M _) _ _ fun y => ?_
  rw [fsum_single, fsum_single, ← Fin.cons_self_tail y, sem_f_M]; simp

theorem pb_M_cons {n : ℕ} (x : (ZMod d)ˣ) (u : Lab d n) :
    pb (Fin.cons 0 u : Lab d (n + 1)) (g1 (Gate.M (lv := lv) x)) = Fin.cons 0 u := by
  refine pb_eq_of _ (isLinW_M _) _ _ fun y => ?_
  rw [← Fin.cons_self_tail y, sem_f_M, fsum_cons, fsum_cons]; ring

theorem pb_SW_zero {m : ℕ} :
    pb (Pi.single 0 1 : Lab d (m + 2)) (g2 (Gate.SWAP (lv := lv))) = Pi.single 1 1 := by
  refine pb_eq_of _ (isLinW_g2 _) _ _ fun y => ?_
  rw [fsum_single, fsum_single, ← Fin.cons_self_tail y, ← Fin.cons_self_tail (Fin.tail y),
    sem_f_SW]; rfl

theorem pb_SW_one {m : ℕ} :
    pb (Pi.single 1 1 : Lab d (m + 2)) (g2 (Gate.SWAP (lv := lv))) = Pi.single 0 1 := by
  refine pb_eq_of _ (isLinW_g2 _) _ _ fun y => ?_
  rw [fsum_single, fsum_single, ← Fin.cons_self_tail y, ← Fin.cons_self_tail (Fin.tail y),
    sem_f_SW]; rfl

theorem pb_SW_cons {m : ℕ} (u : Lab d m) :
    pb (Fin.cons 0 (Fin.cons 0 u) : Lab d (m + 2)) (g2 (Gate.SWAP (lv := lv))) =
      Fin.cons 0 (Fin.cons 0 u) := by
  refine pb_eq_of _ (isLinW_g2 _) _ _ fun y => ?_
  rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail (Fin.tail y), sem_f_SW, fsum_cons,
    fsum_cons, fsum_cons, fsum_cons]; ring

theorem pb_CX_zero {m : ℕ} :
    pb (Pi.single 0 1 : Lab d (m + 2)) (g2 (Gate.CX (lv := lv))) =
      Pi.single 0 1 + Pi.single 1 1 := by
  refine pb_eq_of _ (isLinW_g2 _) _ _ fun y => ?_
  have := sem_f_CX_pow (d := d) (lv := lv) (m := m) 1 (y 0) (y 1) (Fin.tail (Fin.tail y))
  rw [pow_one] at this
  rw [fsum_single, fsum_add, fsum_single, fsum_single]
  conv_lhs => rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail (Fin.tail y)]
  rw [show (Fin.tail y 0) = y 1 from rfl, this]; simp

theorem pb_CX_cons {m : ℕ} (u : Lab d (m + 1)) :
    pb (Fin.cons 0 u : Lab d (m + 2)) (g2 (Gate.CX (lv := lv))) = Fin.cons 0 u := by
  refine pb_eq_of _ (isLinW_g2 _) _ _ fun y => ?_
  have := sem_f_CX_pow (d := d) (lv := lv) (m := m) 1 (y 0) (y 1) (Fin.tail (Fin.tail y))
  rw [pow_one] at this
  conv_lhs => rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail (Fin.tail y)]
  rw [show (Fin.tail y 0) = y 1 from rfl, this, fsum_cons, cons_tail_tail]
  conv_rhs => rw [← Fin.cons_self_tail y]
  rw [fsum_cons]; ring

theorem pb_CX_pow_zero {m : ℕ} (k : ℕ) :
    pb (Pi.single 0 1 : Lab d (m + 2)) (g2 (Gate.CX (lv := lv)) ^ k) =
      Pi.single 0 1 + (k : ZMod d) • Pi.single 1 1 := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_smul, add_zero]
    refine pb_eq_of _ IsLinW.one _ _ fun y => ?_
    rw [fsum_single, fsum_single, map_one]; rfl
  | succ k ih =>
    rw [pow_succ, pb_mul _ _ _ ((isLinW_g2 _).pow k) (isLinW_g2 _), ih, pb_add, pb_smul,
      pb_CX_zero, show (Pi.single 1 1 : Lab d (m + 2)) = Fin.cons 0 (Pi.single 0 1) by
        rw [cons_single]; rfl, pb_CX_cons]
    rw [show (Fin.cons 0 (Pi.single 0 1) : Lab d (m + 2)) = Pi.single 1 1 by rw [cons_single]; rfl]
    push_cast; module

/-! ### Atoms on the forms of two and three wires -/

section Atoms

variable (hA : Admissible d lv) (g : Gate d lv 1)
  (hg : ∀ m : ℕ, Commute (shiftQ (mk (g1 (n := m) g))) (qa (d := d) (lv := lv) m))

include hA hg in
theorem atomL_e01 (m : ℕ) :
    atomL g (Pi.single 0 1 + Pi.single 1 1 : Lab d (m + 2)) = (qa m)⁻¹ * mk (g1 g) * qa m := by
  rw [← pb_CX_zero (lv := lv), ← atomL_conj hA g hg _ _ (isLinW_g2 _), atomL_e0 hA g hg]

include hA hg in
theorem atomL_e0m1 (m : ℕ) :
    atomL g (Pi.single 0 1 - Pi.single 1 1 : Lab d (m + 2)) = qa m * mk (g1 g) * (qa m)⁻¹ := by
  have hk : (((-1 : ZMod d).val : ℕ) : ZMod d) = -1 := ZMod.natCast_zmod_val _
  have e := atomL_conj hA g hg (Pi.single 0 1 : Lab d (m + 2)) (g2 Gate.CX ^ (-1 : ZMod d).val)
    ((isLinW_g2 _).pow _)
  rw [pb_CX_pow_zero, hk, neg_one_smul, ← sub_eq_add_neg, atomL_e0 hA g hg, map_pow,
    qa_neg_one, inv_inv] at e
  exact e.symm

include hA hg in
theorem atomL_e1 (m : ℕ) :
    atomL g (Pi.single 1 1 : Lab d (m + 2)) = mk (shift (g1 (n := m) g)) := by
  rw [show (Pi.single 1 1 : Lab d (m + 2)) = Fin.cons 0 (Pi.single 0 1) by rw [cons_single]; rfl,
    ← shiftQ_atomL hA g hg, atomL_e0 hA g hg]
  rfl

end Atoms

/-! ### `CS` and `CCZ` as products of atoms -/

/-- `CS` on the bottom wires. -/
noncomputable def csQ (h3 : 3 ≤ lv) (m : ℕ) : Q d lv (m + 2) := mk (pad m (CS (d := d) h3))

/-- `CCZ` on the bottom wires. -/
noncomputable def cczQ (h3 : 3 ≤ lv) (m : ℕ) : Q d lv (m + 3) := mk (pad m (CCZ (d := d) h3))

omit [Fact d.Prime] in
theorem pad_pad1 (m : ℕ) (w : C d lv 2) :
    (pad m (pad 1 w : C d lv 3) : C d lv (m + 3)) = pad (m + 1) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    congr 1
    show FreeMonoid.of (Gen.pad m (Gen.pad 1 x)) = FreeMonoid.of (Gen.pad (m + 1) x)
    congr 1
    cases x with
    | gate0 g => rfl
    | gate1 g => rfl
    | gate2 g => rfl
    | up g =>
      cases g with
      | gate0 g => rfl
      | gate1 g => rfl
      | up g => cases g with
        | gate0 g => rfl

/-- Definition 17: `CS` is `T` on `x₀ ∓ x₁` to the powers `∓1/2`, `T⁻¹` on
`x₁`, and quadratic diagonals. -/
theorem csQ_dec (hA : Admissible d lv) (h3 : 3 ≤ lv) (m : ℕ) :
    csQ h3 m = atomL (Gate.T h3) (Pi.single 0 1 - Pi.single 1 1 : Lab d (m + 2)) ^
        (-(2 : ZMod d)⁻¹).val *
      atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 1 1) ^ ((2 : ZMod d)⁻¹).val *
      mk (shift (g1 (n := m) (Gate.S (two_le_of_three h3)))) ^ (-1 : ZMod d).val *
      atomL (Gate.T h3) (Pi.single 1 1) ^ (-1 : ZMod d).val *
      mk (shift (g1 (n := m) (Gate.Z (by omega)))) ^ (-(2 : ZMod d)⁻¹).val *
      czQ (two_le_of_three h3) m ^ ((2 : ZMod d)⁻¹).val := by
  have h1 : ∀ k : ℕ, atomL (Gate.T h3) (Pi.single 0 1 - Pi.single 1 1 : Lab d (m + 2)) ^ k =
      qa m * mk (g1 (Gate.T h3)) ^ k * (qa m)⁻¹ := fun k => by
    rw [atomL_e0m1 hA _ (relT1CX h3), conj_pow]
  have h2 : ∀ k : ℕ, atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 1 1 : Lab d (m + 2)) ^ k =
      (qa m)⁻¹ * mk (g1 (Gate.T h3)) ^ k * qa m := fun k => by
    rw [atomL_e01 hA _ (relT1CX h3), conjInv_pow]
  rw [h1, h2, atomL_e1 hA _ (relT1CX h3)]
  simp only [csQ, czQ, CS, seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1,
    Circuit.pad_g2, pad_shift, qa_neg_one]
  group

/-- Definition 18: `CCZ` is the third difference of `T` on `x₀, x₁, x₂`. -/
theorem cczQ_dec (hA : Admissible d lv) (h3 : 3 ≤ lv) (m : ℕ) :
    cczQ h3 m = atomL (Gate.T h3) (Pi.single 0 1 : Lab d (m + 3)) *
      atomL (Gate.T h3) (Pi.single 1 1) * atomL (Gate.T h3) (Pi.single 2 1) *
      (atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 2 1))⁻¹ *
      (atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 1 1))⁻¹ *
      (atomL (Gate.T h3) (Pi.single 1 1 + Pi.single 2 1))⁻¹ *
      atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1) := by
  have hT := relT1CX (d := d) h3
  have hσ : (mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))))⁻¹ = mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) := by
    show (shiftQ (qs (d := d) (lv := lv) m))⁻¹ = shiftQ (qs m); rw [← map_inv, qs_inv]
  have hσT : mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)) = mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) :=
    (comm1Q (Gate.T h3) (qs (d := d) (lv := lv) m)).eq.symm
  have hσσ : mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) = 1 := by
    have := inv_mul_cancel (mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))))); rwa [hσ] at this
  have hAinv : mk (shift (g2 (n := m) (Gate.CX (d := d) (lv := lv)))) ^ (-1 : ZMod d).val = (mk (shift (g2 (n := m) (Gate.CX (d := d) (lv := lv)))))⁻¹ := by
    show shiftQ (qa (d := d) (lv := lv) m) ^ (-1 : ZMod d).val = (shiftQ (qa m))⁻¹
    rw [← map_pow, qa_neg_one, map_inv]
  have hT0 : atomL (Gate.T h3) (Pi.single 0 1 : Lab d (m + 3)) = mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)) := atomL_e0 hA _ hT _
  have hT1 : atomL (Gate.T h3) (Pi.single 1 1 : Lab d (m + 3)) = mk (shift (g1 (n := m + 1) (Gate.T (d := d) (lv := lv) h3))) :=
    atomL_e1 hA _ hT _
  have hT2 : atomL (Gate.T h3) (Pi.single 2 1 : Lab d (m + 3)) = mk (shift (shift (g1 (n := m) (Gate.T (d := d) (lv := lv) h3)))) := by
    rw [show (Pi.single 2 1 : Lab d (m + 3)) = Fin.cons 0 (Pi.single 1 1) by rw [cons_single]; rfl,
      ← shiftQ_atomL hA _ hT, atomL_e1 hA _ hT]; rfl
  have h01 : atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 1 1 : Lab d (m + 3)) =
      (qa (d := d) (lv := lv) (m + 1))⁻¹ * mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)) * qa (d := d) (lv := lv) (m + 1) := atomL_e01 hA _ hT _
  have h12 : atomL (Gate.T h3) (Pi.single 1 1 + Pi.single 2 1 : Lab d (m + 3)) =
      (mk (shift (g2 (n := m) (Gate.CX (d := d) (lv := lv)))))⁻¹ * mk (shift (g1 (n := m + 1) (Gate.T (d := d) (lv := lv) h3))) * mk (shift (g2 (n := m) (Gate.CX (d := d) (lv := lv)))) := by
    rw [show (Pi.single 1 1 + Pi.single 2 1 : Lab d (m + 3)) =
        Fin.cons 0 (Pi.single 0 1 + Pi.single 1 1) by
      rw [cons_zero_add, cons_single, cons_single]; rfl, ← shiftQ_atomL hA _ hT, atomL_e01 hA _ hT]
    simp only [map_mul, map_inv]; rfl
  have h012 : atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 : Lab d (m + 3)) =
      (mk (shift (g2 (n := m) (Gate.CX (d := d) (lv := lv)))))⁻¹ * ((qa (d := d) (lv := lv) (m + 1))⁻¹ * mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)) * qa (d := d) (lv := lv) (m + 1)) * mk (shift (g2 (n := m) (Gate.CX (d := d) (lv := lv)))) := by
    rw [← h01, atomL_conj hA _ hT _ _ (isLinW_shift (isLinW_g2 _)), pb_add,
      pb_shift_zero _ (isLinW_g2 _),
      show (Pi.single 1 1 : Lab d (m + 3)) = Fin.cons 0 (Pi.single 0 1) by rw [cons_single]; rfl,
      pb_shift_cons _ (isLinW_g2 _), pb_CX_zero, cons_zero_add, cons_single, cons_single,
      add_assoc (Pi.single 0 1 : Lab d (m + 3))]
    rfl
  have h02 : atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 2 1 : Lab d (m + 3)) =
      (mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))))⁻¹ * ((qa (d := d) (lv := lv) (m + 1))⁻¹ * mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)) * qa (d := d) (lv := lv) (m + 1)) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) := by
    have e := atomL_conj hA _ hT (Pi.single 0 1 + Pi.single 1 1 : Lab d (m + 3))
      (shift (g2 (n := m) Gate.SWAP)) (isLinW_shift (isLinW_g2 _))
    have hpb : pb (Pi.single 0 1 + Pi.single 1 1 : Lab d (m + 3))
        (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) = Pi.single 0 1 + Pi.single 2 1 := by
      rw [pb_add, pb_shift_zero _ (isLinW_g2 _),
        show (Pi.single 1 1 : Lab d (m + 3)) = Fin.cons 0 (Pi.single 0 1) by rw [cons_single]; rfl,
        pb_shift_cons _ (isLinW_g2 _), pb_SW_zero, cons_single]
      rfl
    rw [hpb, h01] at e
    exact e.symm
  have h1 : (mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹ * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) = mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hσT, mul_inv_cancel_right]
  have h02' : (atomL (Gate.T h3) (Pi.single 0 1 + Pi.single 2 1 : Lab d (m + 3)))⁻¹ =
      mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (qa (d := d) (lv := lv) (m + 1))⁻¹ * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹ * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * qa (d := d) (lv := lv) (m + 1) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) := by
    rw [h02]
    calc ((mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))))⁻¹ * ((qa (d := d) (lv := lv) (m + 1))⁻¹ * mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)) * qa (d := d) (lv := lv) (m + 1)) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))))⁻¹
        = (mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))))⁻¹ * (qa (d := d) (lv := lv) (m + 1))⁻¹ * (mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹ * qa (d := d) (lv := lv) (m + 1) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) := by group
      _ = mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (qa (d := d) (lv := lv) (m + 1))⁻¹ * (mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹ * qa (d := d) (lv := lv) (m + 1) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) := by rw [hσ]
      _ = mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (qa (d := d) (lv := lv) (m + 1))⁻¹ * (mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))))) * (mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹ * qa (d := d) (lv := lv) (m + 1) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) := by rw [hσσ, mul_one]
      _ = mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (qa (d := d) (lv := lv) (m + 1))⁻¹ * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹) * qa (d := d) (lv := lv) (m + 1) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) := by group
      _ = mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * (qa (d := d) (lv := lv) (m + 1))⁻¹ * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) * ((mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹ * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))))) * qa (d := d) (lv := lv) (m + 1) * mk (shift (g2 (n := m) (Gate.SWAP (d := d) (lv := lv)))) := by rw [h1]
      _ = _ := by group
  have hTinv : mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)) ^ (-1 : ZMod d).val = (mk (g1 (n := m + 2) (Gate.T (d := d) (lv := lv) h3)))⁻¹ := pow_val_neg_one (relTd h3 _) one_lt_d
  have hT1inv : mk (shift (g1 (n := m + 1) (Gate.T (d := d) (lv := lv) h3))) ^ (-1 : ZMod d).val = (mk (shift (g1 (n := m + 1) (Gate.T (d := d) (lv := lv) h3))))⁻¹ := pow_val_neg_one (by
        rw [← shiftQ_mk, ← map_pow, relTd, map_one]) one_lt_d
  rw [hT0, hT1, hT2, h01, h12, h012, h02']
  simp only [cczQ, CCZ, long, seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow,
    Circuit.pad_g1, Circuit.pad_g2, pad_shift, qa_neg_one, hTinv, hT1inv, hAinv]
  group

end QCert.PhaseAffine
