/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The atoms of the quadratic fragment

The phase gates `Z` and `S` placed on a linear form `u · x` (`Psi u`,
`Phi u`): the atoms of `Atom` for the circuit `rowW u`, and `1` for
`u = 0`.  Their algebra, all derived from Figures 1, 3 and 4 of Blake
(arXiv:2603.06466):

* any linear circuit computing `u · x` places them (`atom_S_eq`,
  `atom_Z_eq`), so a linear circuit conjugates an atom into an atom;
* they commute (`atoms_commute`; Lemma 11 of the paper for `Z`, `S`, `CZ`):
  a representative for `u` is `M_{u₀} CX ↑W'`, so the question is whether
  `S` and `Z` commute with `CX⁻¹ S CX` and `CX⁻¹ Z CX` — the latter is
  `Z Z` by (21), and the former is `S` placed on `x₀ + x₁`, which is also
  `S` on wire `1` conjugated by the `CX` from wire `0` to wire `1`;
* `Psi` is additive (by (21) on two independent forms, by (22) on dependent
  ones); `Phi (c u) = Phi u ^ {c²} Psi u ^ {binom c 2}` ((27));
* the parallelogram law `Phi (u + v) Phi (u - v) = Phi u² Phi v² Psi v`, from
  (28), `M_{-1} CZ^{-1} M_{-1} = CZ`, with `CZ` written out by its
  Definition 16 as `S` on `x₀ + x₁` against `S` on `x₀` and on `x₁`.

With these, `QuadDiag` reads every product of atoms as a quadratic form.
-/
import QCert.PhaseAffine.Rows

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

section Quad

variable [Fact d.Prime]

local notation "𝒢" => gateData d lv

/-! ### Local relations -/

omit [Fact d.Prime] in
/-- (29): `S` on the control commutes with `CX`. -/
theorem relS1CX (h2 : 2 ≤ lv) (m : ℕ) :
    Commute (shiftQ (mk (g1 (n := m) (Gate.S (d := d) h2)))) (qa (lv := lv) m) := by
  have e := mk_rule m (Rules.r29 (d := d) (lv := lv) h2)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g2, pad_shift,
    Circuit.pad_g1] at e
  exact e.symm

theorem relZ1CX' (h1 : 1 ≤ lv) (m : ℕ) :
    Commute (shiftQ (mk (g1 (n := m) (Gate.Z (d := d) h1)))) (qa (lv := lv) m) :=
  relZ1CX h1 m

omit [Fact d.Prime] in
theorem relSd (h2 : 2 ≤ lv) (m : ℕ) : mk (g1 (n := m) (Gate.S (d := d) h2)) ^ d = 1 := by
  simpa [Circuit.pad_g1] using mk_rule m (Rules.r24 (d := d) (lv := lv) h2)

omit [Fact d.Prime] in
/-- (26): `S` and `Z` commute. -/
theorem relSZ (h2 : 2 ≤ lv) (m : ℕ) :
    Commute (mk (g1 (n := m) (Gate.S (d := d) h2))) (mk (g1 (Gate.Z (by omega)))) := by
  have e := mk_rule m (Rules.r26 (d := d) (lv := lv) h2)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g1] at e
  exact e

/-- (27): `M_x⁻¹ S M_x = Z^{binom x 2} S^{x²}`. -/
theorem relMS (h2 : 2 ≤ lv) (m : ℕ) (x : (ZMod d)ˣ) :
    (qm m x)⁻¹ * mk (g1 (n := m) (Gate.S (d := d) (lv := lv) h2)) * qm m x =
      mk (g1 (Gate.Z (by omega))) ^ (binom2 (x : ZMod d)).val *
        mk (g1 (Gate.S h2)) ^ ((x : ZMod d) ^ 2).val := by
  have e := mk_rule m (Rules.r27 (d := d) (lv := lv) h2 x)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1] at e
  rw [mul_assoc, e]; group

/-- (22): `M_x⁻¹ Z M_x = Z^x`. -/
theorem relMZ (h1 : 1 ≤ lv) (m : ℕ) (x : (ZMod d)ˣ) :
    (qm m x)⁻¹ * mk (g1 (n := m) (Gate.Z (d := d) (lv := lv) h1)) * qm m x =
      mk (g1 (Gate.Z h1)) ^ (x : ZMod d).val := by
  have e := mk_rule m (Rules.r22 (d := d) (lv := lv) h1 x)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1] at e
  rw [mul_assoc, e]; group

/-- (21): `CX⁻¹ Z₀ CX = Z₀ Z₁`. -/
theorem relCXZ (h1 : 1 ≤ lv) (m : ℕ) :
    (qa (d := d) (lv := lv) m)⁻¹ * mk (g1 (n := m + 1) (Gate.Z h1)) * qa m =
      mk (g1 (Gate.Z h1)) * shiftQ (mk (g1 (n := m) (Gate.Z h1))) := by
  have e := mk_rule m (Rules.r21 (d := d) (lv := lv) h1)
  simp only [seq_cons, seq_nil, one_mul, map_mul, Circuit.pad_g1, Circuit.pad_g2,
    pad_shift] at e
  rw [mul_assoc, ← e]; group; rfl

omit [Fact d.Prime] in
theorem conjInv_pow {G : Type*} [Group G] (p x : G) (k : ℕ) :
    (p⁻¹ * x * p) ^ k = p⁻¹ * x ^ k * p := by
  simpa using conj_pow (a := p⁻¹) (b := x) (i := k)

/-! ### Atoms placed by any linear circuit -/

theorem row_ne_zero (hA : Admissible d lv) {n : ℕ} (W : C d lv (n + 1)) (u : Lab d (n + 1))
    (hu : ∀ y, ((𝒢).sem (n + 1) W).f y 0 = ∑ j, u j * y j) : u ≠ 0 := by
  rintro rfl
  obtain ⟨y, hy⟩ := sem_surj hA W (Pi.single 0 1)
  have := hu y
  rw [hy] at this
  simp at this

/-- An atom on a linear form, `1` on the zero form. -/
noncomputable def atomL (g : Gate d lv 1) {n : ℕ} (u : Lab d (n + 1)) : Q d lv (n + 1) :=
  if u = 0 then 1 else atom g (rowW n u)

theorem atom_eq_atomL (hA : Admissible d lv) (g : Gate d lv 1)
    (hg : ∀ m : ℕ, Commute (shiftQ (mk (g1 (n := m) g))) (qa (d := d) (lv := lv) m))
    {n : ℕ} (W : C d lv (n + 1)) (hW : IsLinW W) (u : Lab d (n + 1))
    (hu : ∀ y, ((𝒢).sem (n + 1) W).f y 0 = ∑ j, u j * y j) : atom g W = atomL g u := by
  have hu0 := row_ne_zero hA W u hu
  rw [atomL, if_neg hu0]
  exact atom_wd hA g hg hW (isLinW_rowW n u) fun y => by rw [hu, sem_rowW n u hu0 y]

theorem atomL_zero (g : Gate d lv 1) {n : ℕ} : atomL g (0 : Lab d (n + 1)) = 1 := if_pos rfl

omit [Fact d.Prime] in
/-- The first coordinate after a gate. -/
theorem sem_f_of_mul {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsAff) (W : C d lv n) (y : Lab d n) :
    ((𝒢).sem n (FreeMonoid.of x * W)).f y = affMap x (((𝒢).sem n W).f y) := by
  rw [sem_f_mul, GateData.sem_of, gen_f x hx]

theorem atom_one (g : Gate d lv 1) {n : ℕ} : atom g (1 : C d lv (n + 1)) = mk (g1 g) := by
  simp [atom]

theorem atomL_e0 (hA : Admissible d lv) (g : Gate d lv 1)
    (hg : ∀ m : ℕ, Commute (shiftQ (mk (g1 (n := m) g))) (qa (d := d) (lv := lv) m)) (n : ℕ) :
    atomL g (Pi.single 0 1 : Lab d (n + 1)) = mk (g1 g) := by
  rw [← atom_eq_atomL hA g hg 1 IsLinW.one, atom_one]
  intro y; simp [Pi.single_apply]

/-- Conjugating an atom by a linear circuit. -/
theorem atom_conj (g : Gate d lv 1) {n : ℕ} (W V : C d lv (n + 1)) :
    (mk V)⁻¹ * atom g W * mk V = atom g (W * V) := by
  simp only [atom, map_mul, mul_inv_rev]; group

/-- An atom one wire up. -/
theorem shiftQ_atom (g : Gate d lv 1) {n : ℕ} (W : C d lv (n + 1)) :
    shiftQ (atom g W) = atom g (g2 Gate.SWAP * shift W) := by
  have h1 : mk (g2 (n := n) (Gate.SWAP (d := d) (lv := lv))) * mk (g1 g) =
      mk (shift (g1 g)) * mk (g2 Gate.SWAP) := relSWnat n g
  have hs : (mk (g2 (n := n) (Gate.SWAP (d := d) (lv := lv))))⁻¹ = mk (g2 Gate.SWAP) :=
    qs_inv n
  have h1' : mk (shift (g1 (n := n) g)) =
      mk (g2 Gate.SWAP) * mk (g1 g) * (mk (g2 (n := n) Gate.SWAP))⁻¹ := by
    rw [h1, mul_inv_cancel_right]
  simp only [atom, map_mul, map_inv, shiftQ_mk]
  rw [h1']
  simp only [mul_inv_rev, hs]
  group

theorem shiftQ_atomL (hA : Admissible d lv) (g : Gate d lv 1)
    (hg : ∀ m : ℕ, Commute (shiftQ (mk (g1 (n := m) g))) (qa (d := d) (lv := lv) m))
    {n : ℕ} (u : Lab d (n + 1)) : shiftQ (atomL g u) = atomL g (Fin.cons 0 u : Lab d (n + 2)) := by
  by_cases hu : u = 0
  · subst hu; rw [atomL_zero, map_one, show (Fin.cons 0 0 : Lab d (n + 2)) = 0 by
      funext i; refine Fin.cases rfl (fun j => rfl) i, atomL_zero]
  rw [atomL, if_neg hu, shiftQ_atom]
  refine atom_eq_atomL hA g hg _ ((isLinW_g2 _).mul (isLinW_shift (isLinW_rowW _ _))) _ ?_
  intro y
  rw [(sem_SW_mul _ y).1]
  conv_lhs => rw [← Fin.cons_self_tail y, sem_f_shift]
  rw [Fin.cons_one, sem_rowW n u hu, sum_cons (Fin.cons 0 u) y]
  simp only [Fin.cons_zero, zero_mul, zero_add, Fin.tail_cons]

/-- The order of an atom divides `d`. -/
theorem atom_pow_d (g : Gate d lv 1) (hd : ∀ m : ℕ, mk (g1 (n := m) g) ^ d = 1) {n : ℕ}
    (W : C d lv (n + 1)) : atom g W ^ d = 1 := by
  rw [atom, show (mk W)⁻¹ * mk (g1 g) * mk W = (mk W)⁻¹ * mk (g1 g) * ((mk W)⁻¹)⁻¹ by
    rw [inv_inv], conj_pow, hd, mul_one, mul_inv_cancel]

theorem atomL_pow_d (g : Gate d lv 1) (hd : ∀ m : ℕ, mk (g1 (n := m) g) ^ d = 1) {n : ℕ}
    (u : Lab d (n + 1)) : atomL g u ^ d = 1 := by
  rw [atomL]; split_ifs
  · exact one_pow _
  · exact atom_pow_d g hd _

/-! ### Atoms commute -/

/-- The hypotheses on a phase gate on wire `0` used for commutation: it
commutes with `CX` on its control, with `S` and with `Z`. -/
structure PhaseGate (h2 : 2 ≤ lv) (g : Gate d lv 1) : Prop where
  ctrl : ∀ m : ℕ, Commute (shiftQ (mk (g1 (n := m) g))) (qa (d := d) (lv := lv) m)
  withS : ∀ m : ℕ, Commute (mk (g1 (n := m) g)) (mk (g1 (Gate.S h2)))
  withZ : ∀ m : ℕ, Commute (mk (g1 (n := m) g)) (mk (g1 (Gate.Z (by omega))))
  /-- `M_x⁻¹ g M_x` is a word in `Z` and `S`. -/
  mul : ∀ (m : ℕ) (x : (ZMod d)ˣ), ∃ a b : ℕ,
    (qm m x)⁻¹ * mk (g1 (n := m) g) * qm m x =
      mk (g1 (Gate.Z (by omega))) ^ a * mk (g1 (Gate.S h2)) ^ b

theorem phaseGate_S (h2 : 2 ≤ lv) : PhaseGate (d := d) h2 (Gate.S h2) where
  ctrl := relS1CX h2
  withS _ := Commute.refl _
  withZ m := relSZ h2 m
  mul m x := ⟨_, _, relMS h2 m x⟩

theorem phaseGate_Z (h2 : 2 ≤ lv) : PhaseGate (d := d) h2 (Gate.Z (by omega)) where
  ctrl := relZ1CX' _
  withS m := (relSZ h2 m).symm
  withZ _ := Commute.refl _
  mul m x := ⟨(x : ZMod d).val, 0, by rw [relMZ, pow_zero, mul_one]⟩

theorem commute_conj_of {G : Type*} [Group G] {x y p : G} (h : Commute x y) :
    Commute (p⁻¹ * x * p) (p⁻¹ * y * p) := by
  show p⁻¹ * x * p * (p⁻¹ * y * p) = p⁻¹ * y * p * (p⁻¹ * x * p)
  calc p⁻¹ * x * p * (p⁻¹ * y * p) = p⁻¹ * (x * y) * p := by group
    _ = p⁻¹ * (y * x) * p := by rw [h.eq]
    _ = _ := by group

/-- `S` on `x₀ + x₁`, written by the `CX` from wire `0` to wire `1`. -/
theorem atom_CX_eq (hA : Admissible d lv) (h2 : 2 ≤ lv) (g' : Gate d lv 1)
    (hg' : PhaseGate h2 g') (m : ℕ) :
    (qa (d := d) (lv := lv) m)⁻¹ * mk (g1 g') * qa m =
      (qs m * qa m * qs m)⁻¹ * shiftQ (mk (g1 (n := m) g')) * (qs m * qa m * qs m) := by
  have e := atom_wd hA g' hg'.ctrl (W := g2 Gate.CX) (W' := g2 Gate.SWAP * abarW 1)
    (isLinW_g2 _) ((isLinW_g2 _).mul (isLinW_abarW _)) (by
      intro y
      rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail (Fin.tail y), sem_f_mul, sem_abarW,
        sem_f_SW, GateData.sem_of, gen_f (Gen.gate2 (n := m) Gate.CX) (by exact trivial)]
      simp [affMap]; ring)
  have e' : (qa (d := d) (lv := lv) m)⁻¹ * mk (g1 g') * qa m =
      (qs m * (qs m * qa m * qs m))⁻¹ * mk (g1 g') * (qs m * (qs m * qa m * qs m)) := by
    have := e
    simp only [atom, map_mul, abarW, map_pow, val_one_zmod, pow_one] at this
    exact this
  rw [e']
  have h1 : qs (d := d) (lv := lv) m * mk (g1 g') = shiftQ (mk (g1 g')) * qs m := relSWnat m g'
  have hs : (qs (d := d) (lv := lv) m)⁻¹ = qs m := qs_inv m
  calc (qs m * (qs m * qa m * qs m))⁻¹ * mk (g1 g') * (qs m * (qs m * qa m * qs m))
      = (qs m * qa m * qs m)⁻¹ * (qs m * mk (g1 g') * (qs m)⁻¹) * (qs m * qa m * qs m) := by
        rw [show qs (d := d) (lv := lv) m * (qs m * qa m * qs m) = qa m * qs m by
          rw [← mul_assoc, ← mul_assoc, qs_mul_self, one_mul]]
        group
    _ = _ := by rw [h1, mul_inv_cancel_right]

/-- A phase gate on wire `0` commutes with `S` and `Z` placed on
`x₀ + x₁`. -/
theorem commute_CX_atom (hA : Admissible d lv) (h2 : 2 ≤ lv) {g g' : Gate d lv 1}
    (hg : PhaseGate h2 g) (hg' : PhaseGate h2 g') (m : ℕ) :
    Commute (mk (g1 (n := m + 1) g)) ((qa (d := d) (lv := lv) m)⁻¹ * mk (g1 g') * qa m) := by
  rw [atom_CX_eq hA h2 g' hg' m]
  have h1 : Commute (mk (g1 (n := m + 1) g)) (qs m * qa m * qs m) := commute_abar g (hg.ctrl m)
  have h2' : Commute (mk (g1 (n := m + 1) g)) (shiftQ (mk (g1 (n := m) g'))) := comm1Q _ _
  exact (h1.inv_right.mul_right h2').mul_right h1

/-- A phase gate on wire `0` commutes with every atom. -/
theorem commute_atom0 (hA : Admissible d lv) (h2 : 2 ≤ lv) {g g' : Gate d lv 1}
    (hg : PhaseGate h2 g) (hg' : PhaseGate h2 g') {n : ℕ} (W : C d lv (n + 1))
    (hW : IsLinW W) : Commute (mk (g1 (n := n) g)) (atom g' W) := by
  rw [atom_eq_atomL hA g' hg'.ctrl W hW (rowv W) (sem_row W hW)]
  -- the words in `Z` and `S` on wire `0`
  have hZS : ∀ (m : ℕ) (a b : ℕ), Commute (mk (g1 (n := m) g))
      (mk (g1 (Gate.Z (by omega))) ^ a * mk (g1 (Gate.S h2)) ^ b) :=
    fun m a b => ((hg.withZ m).pow_right a).mul_right ((hg.withS m).pow_right b)
  generalize rowv W = u
  rw [atomL]
  split_ifs with hu
  · exact Commute.one_right _
  cases n with
  | zero =>
    obtain ⟨a, b, e⟩ := hg'.mul 0 (unitOf (u 0))
    rw [rowW, atom, e]; exact hZS 0 a b
  | succ n =>
    by_cases h0 : u 0 = 0
    · rw [rowW, if_pos h0, ← shiftQ_atom]; exact comm1Q _ _
    -- the representative `M_{u₀} CX ↑W'`
    obtain ⟨a, b, e⟩ := hg'.mul (n + 1) (unitOf (u 0))
    by_cases ht : Fin.tail u = 0
    · rw [rowW, if_neg h0, ht, smul_zero]
      simp only [atom, map_mul]
      rw [show mk (fanW (lv := lv) (n + 1) 0) = 1 from fan_zero (n + 1), mul_one, e]
      exact hZS _ a b
    set c := (u 0)⁻¹ • Fin.tail u
    have hc : c ≠ 0 := by
      intro hc; apply ht
      have : (u 0) • c = Fin.tail u := by rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
      rw [← this, hc, smul_zero]
    have hW' : IsLinW (g1 (Gate.M (unitOf (u 0))) * g2 Gate.CX * shift (rowW n c) :
        C d lv (n + 2)) :=
      ((isLinW_M _).mul (isLinW_g2 _)).mul (isLinW_shift (isLinW_rowW _ _))
    have hrow : ∀ y, ((𝒢).sem (n + 2) (g1 (Gate.M (unitOf (u 0))) * g2 Gate.CX *
        shift (rowW n c))).f y 0 = ∑ j, u j * y j := by
      intro y
      have hsh : ((𝒢).sem (n + 2) (shift (rowW n c))).f y =
          Fin.cons (y 0) (((𝒢).sem (n + 1) (rowW n c)).f (Fin.tail y)) := by
        conv_lhs => rw [← Fin.cons_self_tail y]
        rw [sem_f_shift]
      rw [mul_assoc, sem_f_of_mul _ (by exact trivial), sem_f_of_mul _ (by exact trivial), hsh]
      simp only [affMap, Fin.cons_zero, Fin.cons_one]
      rw [sem_rowW n c hc, unitOf_val h0, sum_cons u]
      simp only [c, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, ← mul_assoc,
        mul_inv_cancel₀ h0, one_mul]
    rw [atom_wd hA g' hg'.ctrl (isLinW_rowW _ _) hW' (fun y => by rw [sem_rowW _ u hu y, hrow y])]
    simp only [atom, map_mul]
    rw [show (mk (g1 (Gate.M (unitOf (u 0)))) * mk (g2 Gate.CX) * mk (shift (rowW n c)))⁻¹ *
        mk (g1 g') * (mk (g1 (Gate.M (unitOf (u 0)))) * mk (g2 Gate.CX) *
        mk (shift (rowW n c))) = (mk (shift (rowW n c)))⁻¹ * ((mk (g2 Gate.CX))⁻¹ *
        ((qm (n + 1) (unitOf (u 0)))⁻¹ * mk (g1 g') * qm (n + 1) (unitOf (u 0))) *
        mk (g2 Gate.CX)) * mk (shift (rowW n c)) by group, e]
    have hR : Commute (mk (g1 (n := n + 1) g)) (mk (shift (rowW n c))) := comm1Q g (mk (rowW n c))
    have hX : Commute (mk (g1 (n := n + 1) g)) ((qa n)⁻¹ * (mk (g1 (Gate.Z (by omega))) ^ a *
        mk (g1 (Gate.S h2)) ^ b) * qa n) := by
      rw [show (qa (d := d) (lv := lv) n)⁻¹ * (mk (g1 (Gate.Z (by omega))) ^ a *
          mk (g1 (Gate.S h2)) ^ b) * qa n = ((qa n)⁻¹ * mk (g1 (Gate.Z (by omega))) * qa n) ^ a *
          ((qa n)⁻¹ * mk (g1 (Gate.S h2)) * qa n) ^ b by
        rw [conjInv_pow, conjInv_pow]; group]
      exact ((commute_CX_atom hA h2 hg (phaseGate_Z h2) n).pow_right a).mul_right
        ((commute_CX_atom hA h2 hg (phaseGate_S h2) n).pow_right b)
    exact (hR.inv_right.mul_right hX).mul_right hR

/-- Atoms commute. -/
theorem atoms_commute (hA : Admissible d lv) (h2 : 2 ≤ lv) {g g' : Gate d lv 1}
    (hg : PhaseGate h2 g) (hg' : PhaseGate h2 g') {n : ℕ} (W W' : C d lv (n + 1))
    (hW : IsLinW W) (hW' : IsLinW W') : Commute (atom g W) (atom g' W') := by
  obtain ⟨V, hV, e⟩ := linInv W hW
  have hVi : mk V = (mk W)⁻¹ := by rw [map_mul] at e; exact eq_inv_of_mul_eq_one_left e
  have h := commute_atom0 hA h2 hg hg' (W' * V) (hW'.mul hV)
  rw [← atom_conj, hVi, inv_inv] at h
  have := commute_conj_of (p := mk W) h
  simp only [atom] at this ⊢
  calc (mk W)⁻¹ * mk (g1 g) * mk W * ((mk W')⁻¹ * mk (g1 g') * mk W')
      = (mk W)⁻¹ * mk (g1 g) * mk W * ((mk W)⁻¹ * (mk W * ((mk W')⁻¹ * mk (g1 g') * mk W') *
        (mk W)⁻¹) * mk W) := by group
    _ = (mk W)⁻¹ * (mk W * ((mk W')⁻¹ * mk (g1 g') * mk W') * (mk W)⁻¹) * mk W *
        ((mk W)⁻¹ * mk (g1 g) * mk W) := this.eq
    _ = _ := by group

theorem atomL_commute (hA : Admissible d lv) (h2 : 2 ≤ lv) {g g' : Gate d lv 1}
    (hg : PhaseGate h2 g) (hg' : PhaseGate h2 g') {n : ℕ} (u v : Lab d (n + 1)) :
    Commute (atomL g u) (atomL g' v) := by
  rw [atomL, atomL]
  split_ifs
  · exact Commute.one_left _
  · exact Commute.one_left _
  · exact Commute.one_right _
  · exact atoms_commute hA h2 hg hg' _ _ (isLinW_rowW _ _) (isLinW_rowW _ _)

/-! ### Scaling, additivity and the parallelogram law -/

theorem binom2_neg_one (hd2 : (2 : ZMod d) ≠ 0) : binom2 (-1 : ZMod d) = 1 := by
  unfold binom2; field_simp; ring

/-- (27) on a form: `S` on `c u` is `S^{c²} Z^{binom c 2}` on `u`. -/
theorem atomL_S_smul (hA : Admissible d lv) (h2 : 2 ≤ lv) {n : ℕ} (c : ZMod d)
    (u : Lab d (n + 1)) :
    atomL (Gate.S h2) (c • u) =
      atomL (Gate.Z (by omega)) u ^ (binom2 c).val * atomL (Gate.S h2) u ^ (c ^ 2).val := by
  by_cases hu : u = 0
  · subst hu; simp [atomL_zero]
  by_cases hc : c = 0
  · subst hc; simp [atomL_zero, binom2]
  have hcu : c • u ≠ 0 := smul_ne_zero hc hu
  rw [← atom_eq_atomL hA (Gate.S h2) (relS1CX h2) (g1 (Gate.M (unitOf c)) * rowW n u)
    ((isLinW_M _).mul (isLinW_rowW _ _)) (c • u) (by
      intro y
      rw [sem_f_of_mul _ (by exact trivial)]
      simp only [affMap, Fin.cons_zero]
      rw [sem_rowW n u hu y, unitOf_val hc, Finset.mul_sum]
      simp [mul_assoc])]
  rw [atomL, atomL, if_neg hu, if_neg hu]
  simp only [atom, map_mul, mul_inv_rev]
  rw [show (mk (rowW n u))⁻¹ * (qm n (unitOf c))⁻¹ * mk (g1 (Gate.S h2)) *
      (qm n (unitOf c) * mk (rowW n u)) = (mk (rowW n u))⁻¹ * ((qm n (unitOf c))⁻¹ *
      mk (g1 (Gate.S h2)) * qm n (unitOf c)) * mk (rowW n u) by group, relMS h2 n (unitOf c),
    unitOf_val hc, conjInv_pow, conjInv_pow]
  group

/-- (22) on a form. -/
theorem atomL_Z_smul (hA : Admissible d lv) (h1 : 1 ≤ lv) {n : ℕ} (c : ZMod d)
    (u : Lab d (n + 1)) :
    atomL (Gate.Z h1) (c • u) = atomL (Gate.Z h1) u ^ c.val := by
  by_cases hu : u = 0
  · subst hu; simp [atomL_zero]
  by_cases hc : c = 0
  · subst hc; simp [atomL_zero]
  rw [← atom_eq_atomL hA (Gate.Z h1) (relZ1CX' h1) (g1 (Gate.M (unitOf c)) * rowW n u)
    ((isLinW_M _).mul (isLinW_rowW _ _)) (c • u) (by
      intro y
      rw [sem_f_of_mul _ (by exact trivial)]
      simp only [affMap, Fin.cons_zero]
      rw [sem_rowW n u hu y, unitOf_val hc, Finset.mul_sum]
      simp [mul_assoc])]
  rw [atomL, if_neg hu]
  simp only [atom, map_mul, mul_inv_rev]
  rw [show (mk (rowW n u))⁻¹ * (qm n (unitOf c))⁻¹ * mk (g1 (Gate.Z h1)) *
      (qm n (unitOf c) * mk (rowW n u)) = (mk (rowW n u))⁻¹ * ((qm n (unitOf c))⁻¹ *
      mk (g1 (Gate.Z h1)) * qm n (unitOf c)) * mk (rowW n u) by group, relMZ h1 n (unitOf c),
    unitOf_val hc, conjInv_pow]

theorem indep_width_one {u v : Lab d 1} (h : Indep u v) : False := by
  apply h.ne_zero
  have := (h (v 0) (-u 0) (by funext i; rw [Fin.fin_one_eq_zero i]; simp; ring)).2
  funext i; rw [Fin.fin_one_eq_zero i]; simpa using this

/-- (21) on two forms: `Z` is additive. -/
theorem atomL_Z_add (hA : Admissible d lv) (h1 : 1 ≤ lv) {n : ℕ} (u v : Lab d (n + 1)) :
    atomL (Gate.Z h1) (u + v) = atomL (Gate.Z h1) u * atomL (Gate.Z h1) v := by
  have hd : ∀ m : ℕ, mk (g1 (n := m) (Gate.Z (d := d) (lv := lv) h1)) ^ d = 1 := relZd h1
  by_cases hu : u = 0
  · subst hu; simp [atomL_zero]
  rcases dep_or_indep u v hu with ⟨c, rfl⟩ | h
  · rw [show u + c • u = (1 + c) • u by rw [add_smul, one_smul], atomL_Z_smul hA h1,
      atomL_Z_smul hA h1, pow_val_add (atomL_pow_d _ hd u), pow_val_one one_lt_d]
  cases n with
  | zero => exact (indep_width_one h).elim
  | succ n =>
    have hr := sem_row2W (lv := lv) n u v h
    set W := row2W (lv := lv) n u v
    have hW := isLinW_row2W (lv := lv) n u v
    rw [← atom_eq_atomL hA _ (relZ1CX' h1) (g2 Gate.CX * W) ((isLinW_g2 _).mul hW) (u + v) (by
        intro y
        rw [sem_f_of_mul _ (by exact trivial)]
        simp only [affMap, Fin.cons_zero, (hr y).1, (hr y).2, Pi.add_apply, add_mul,
          Finset.sum_add_distrib]),
      ← atom_eq_atomL hA _ (relZ1CX' h1) W hW u (fun y => (hr y).1),
      ← atom_eq_atomL hA _ (relZ1CX' h1) (g2 Gate.SWAP * W) ((isLinW_g2 _).mul hW) v (by
        intro y
        rw [sem_f_of_mul _ (by exact trivial)]
        simp only [affMap, Fin.cons_zero, (hr y).2])]
    have hs : (qs (d := d) (lv := lv) n)⁻¹ = qs n := qs_inv n
    have h1' : qs (d := d) (lv := lv) n * mk (g1 (Gate.Z h1)) =
        shiftQ (mk (g1 (n := n) (Gate.Z h1))) * qs n := relSWnat n _
    simp only [atom, map_mul, mul_inv_rev]
    rw [show (mk W)⁻¹ * (mk (g2 Gate.CX))⁻¹ * mk (g1 (Gate.Z h1)) * (mk (g2 Gate.CX) * mk W) =
      (mk W)⁻¹ * ((qa n)⁻¹ * mk (g1 (Gate.Z h1)) * qa n) * mk W by group, relCXZ h1 n,
      show shiftQ (mk (g1 (n := n) (Gate.Z (d := d) (lv := lv) h1))) =
        qs n * mk (g1 (Gate.Z h1)) * (qs n)⁻¹ by rw [h1', mul_inv_cancel_right], hs]
    group

/-! ### `CZ` and rule (28) -/

/-- `CZ` on the bottom two wires (Definition 16). -/
noncomputable def czQ (h2 : 2 ≤ lv) (m : ℕ) : Q d lv (m + 2) := mk (pad m (CZ (d := d) h2))

theorem czQ_eq (h2 : 2 ≤ lv) (m : ℕ) :
    czQ (d := d) h2 m = (mk (g1 (n := m + 1) (Gate.S h2)))⁻¹ *
      (mk (shift (g1 (n := m) (Gate.S h2))))⁻¹ * (qa m)⁻¹ * mk (g1 (Gate.S h2)) * qa m := by
  have hS0 : mk (g1 (n := m + 1) (Gate.S (d := d) (lv := lv) h2)) ^ (-1 : ZMod d).val =
      (mk (g1 (Gate.S h2)))⁻¹ := pow_val_neg_one (relSd h2 (m + 1)) one_lt_d
  have hS1 : mk (shift (g1 (n := m) (Gate.S (d := d) (lv := lv) h2))) ^ (-1 : ZMod d).val =
      (mk (shift (g1 (Gate.S h2))))⁻¹ := pow_val_neg_one (by
        rw [← shiftQ_mk, ← map_pow, relSd, map_one]) one_lt_d
  have hA : mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) ^ (-1 : ZMod d).val =
      (mk (g2 Gate.CX))⁻¹ := qa_neg_one m
  simp only [czQ, CZ, seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1,
    Circuit.pad_g2, pad_shift, hS0, hS1, hA]

/-- Rule (28): `M_{-1}` on wire `1` conjugates `CZ` to its inverse. -/
theorem rel28 (h2 : 2 ≤ lv) (m : ℕ) :
    shiftQ (qm (d := d) (lv := lv) m (-1)) * czQ h2 m ^ (-1 : ZMod d).val *
      shiftQ (qm m (-1)) = czQ h2 m := by
  have e := mk_rule m (Rules.r28 (d := d) (lv := lv) h2)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, Circuit.pad_g1, pad_shift] at e
  simpa [czQ, mul_assoc] using e

/-- The parallelogram law for two independent forms, before rearranging:
`CZ` conjugated by a circuit for `(u, v)` and by one for `(u, -v)`. -/
theorem par_raw (hA : Admissible d lv) (h2 : 2 ≤ lv) {n : ℕ} (u v : Lab d (n + 2))
    (h : Indep u v) :
    (atomL (Gate.S h2) u)⁻¹ * (atomL (Gate.S h2) v)⁻¹ * atomL (Gate.S h2) (u + v) =
      ((atomL (Gate.S h2) u)⁻¹ * (atomL (Gate.S h2) (-v))⁻¹ * atomL (Gate.S h2) (u - v)) ^
        (-1 : ZMod d).val := by
  have hr := sem_row2W (lv := lv) n u v h
  set W := row2W (lv := lv) n u v
  have hW := isLinW_row2W (lv := lv) n u v
  set W2 : C d lv (n + 2) := shift (g1 (Gate.M (-1))) * W
  have hW2 : IsLinW W2 := (isLinW_shift (isLinW_M _)).mul hW
  have hr2 : ∀ y, ((𝒢).sem (n + 2) W2).f y 0 = ∑ j, u j * y j ∧
      ((𝒢).sem (n + 2) W2).f y 1 = ∑ j, (-v) j * y j := by
    intro y
    rw [show W2 = FreeMonoid.of (Gen.up (Gen.gate1 (Gate.M (-1)))) * W by rfl,
      sem_f_of_mul _ (by exact trivial)]
    simp only [affMap, Fin.cons_zero, Fin.cons_one, Fin.tail]
    refine ⟨(hr y).1, ?_⟩
    simp only [Units.val_neg, Units.val_one, neg_mul, one_mul, Pi.neg_apply,
      Finset.sum_neg_distrib]
    rw [← (hr y).2]; rfl
  have eS := fun (V : C d lv (n + 2)) (hV : IsLinW V) (w : Lab d (n + 2))
    (hw : ∀ y, ((𝒢).sem (n + 2) V).f y 0 = ∑ j, w j * y j) =>
    atom_eq_atomL hA (Gate.S h2) (relS1CX h2) V hV w hw
  have rowCX : ∀ (V : C d lv (n + 2)) (a b : Lab d (n + 2)),
      (∀ y, ((𝒢).sem (n + 2) V).f y 0 = ∑ j, a j * y j ∧
        ((𝒢).sem (n + 2) V).f y 1 = ∑ j, b j * y j) →
      ∀ y, ((𝒢).sem (n + 2) (g2 Gate.CX * V)).f y 0 = ∑ j, (a + b) j * y j := by
    intro V a b hab y
    rw [sem_f_of_mul _ (by exact trivial)]
    simp only [affMap, Fin.cons_zero, (hab y).1, (hab y).2, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  have rowSW : ∀ (V : C d lv (n + 2)) (a b : Lab d (n + 2)),
      (∀ y, ((𝒢).sem (n + 2) V).f y 0 = ∑ j, a j * y j ∧
        ((𝒢).sem (n + 2) V).f y 1 = ∑ j, b j * y j) →
      ∀ y, ((𝒢).sem (n + 2) (g2 Gate.SWAP * V)).f y 0 = ∑ j, b j * y j := by
    intro V a b hab y
    rw [sem_f_of_mul _ (by exact trivial)]
    simp only [affMap, Fin.cons_zero, (hab y).2]
  -- `CZ` conjugated by a circuit `V` for `(a, b)`
  have hconj : ∀ (V : C d lv (n + 2)), IsLinW V → ∀ a b : Lab d (n + 2),
      (∀ y, ((𝒢).sem (n + 2) V).f y 0 = ∑ j, a j * y j ∧
        ((𝒢).sem (n + 2) V).f y 1 = ∑ j, b j * y j) →
      (mk V)⁻¹ * czQ h2 n * mk V = (atomL (Gate.S h2) a)⁻¹ * (atomL (Gate.S h2) b)⁻¹ *
        atomL (Gate.S h2) (a + b) := by
    intro V hV a b hab
    rw [← eS V hV a (fun y => (hab y).1), ← eS _ ((isLinW_g2 _).mul hV) b (rowSW V a b hab),
      ← eS _ ((isLinW_g2 _).mul hV) (a + b) (rowCX V a b hab), czQ_eq]
    have hS1 : mk (shift (g1 (n := n) (Gate.S (d := d) (lv := lv) h2))) =
        mk (g2 Gate.SWAP) * mk (g1 (Gate.S h2)) * mk (g2 Gate.SWAP) := by
      calc mk (shift (g1 (n := n) (Gate.S (d := d) (lv := lv) h2)))
          = mk (shift (g1 (Gate.S h2))) * mk (g2 Gate.SWAP) * mk (g2 Gate.SWAP) := by
            rw [mul_assoc, relSW2, mul_one]
        _ = _ := by rw [← relSWnat]
    have hs : (mk (g2 (n := n) (Gate.SWAP (d := d) (lv := lv))))⁻¹ = mk (g2 Gate.SWAP) :=
      qs_inv n
    rw [hS1]
    simp only [atom, map_mul, mul_inv_rev, hs]
    group
  have hm : (shiftQ (qm (d := d) (lv := lv) n (-1)))⁻¹ = shiftQ (qm n (-1)) := by
    rw [qmt_inv, inv_neg, inv_one]
  have hW2m : mk W2 = shiftQ (qm (d := d) (lv := lv) n (-1)) * mk W := by
    rw [show W2 = shift (g1 (Gate.M (-1))) * W from rfl, map_mul]; rfl
  rw [sub_eq_add_neg, ← hconj W hW u v hr, ← hconj W2 hW2 u (-v) hr2, conjInv_pow, hW2m]
  conv_lhs => rw [← rel28 h2 n]
  rw [mul_inv_rev, hm]
  group

end Quad

end QCert.PhaseAffine
