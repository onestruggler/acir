/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Separating interpretations (Section 5.3)

The two kinds of model of Figure 8:

* *Weighted counts* (Definitions 26, 28, 29, 30 and 35): each gate has a
  weight in a commutative monoid `M`, the swap a weight `ε` with `ε + ε = 0`,
  and a circuit weighs the sum of its gates (`countModel`).  The occurrence
  detector `?g` takes `M = Occ` (`{0, 1}` under `∨`), the counts `#{…}_[m]`
  take `M = ZMod m`, and `arg det_k` takes `M = ZMod 8` (angles in units of
  `π/4`).
* *Projective substitutions* (Definitions 32–34): matrices over a ring `K`
  compared up to a unit scalar (`projModel`); the matrices of the gates may
  be any, a substituted gate getting the matrix of the substituted circuit.

Both are `Model`s of the PROP structure (Lemma 25).  For a matrix model the
structural rules hold for every gate set (`Ops.eval_shift`,
`Ops.eval_pad` and the commutations), and the laws of the symmetry are
checked gate by gate.
-/
import QCert.Minimality.Basic
import QCert.Minimality.Trie

namespace QCert.Minimality

open Circuit Matrix

variable {Gate : ℕ → Type}

/-! ### Weighted counts -/

/-- A weight for each gate. -/
structure Weights (Gate : ℕ → Type) (M : Type*) where
  w0 : Gate 0 → M
  w1 : Gate 1 → M
  w2 : Gate 2 → M
  w3 : Gate 3 → M

namespace Weights

variable {M : Type*} [AddCommMonoid M] (W : Weights Gate M)

/-- The weight of a generator. -/
def gen : {n : ℕ} → Gen Gate n → M
  | _, .gate0 g => W.w0 g
  | _, .gate1 g => W.w1 g
  | _, .gate2 g => W.w2 g
  | _, .gate3 g => W.w3 g
  | _, .up g => gen g

/-- The weight of a circuit, the sum of the weights of its gates. -/
def hom (n : ℕ) : Circuit Gate n →* Multiplicative M := FreeMonoid.lift fun g => .ofAdd (W.gen g)

theorem hom_of {n : ℕ} (g : Gen Gate n) : W.hom n (FreeMonoid.of g) = .ofAdd (W.gen g) :=
  FreeMonoid.lift_eval_of _ _

theorem hom_shift {n : ℕ} (w : Circuit Gate n) : W.hom (n + 1) (shift w) = W.hom n w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, shift_of, ih, map_mul]
    simp only [hom_of]
    rfl

omit [AddCommMonoid M] in
theorem gen_pad (m : ℕ) {k : ℕ} (g : Gen Gate k) : W.gen (g.pad m) = W.gen g := by
  induction g with
  | gate0 c => rfl
  | gate1 c => rfl
  | gate2 c => rfl
  | gate3 c => rfl
  | up g ih => exact ih

theorem hom_pad (m : ℕ) {k : ℕ} (w : Circuit Gate k) : W.hom (m + k) (Circuit.pad m w) = W.hom k w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    show W.hom (m + k) (FreeMonoid.of (g.pad m)) * _ = _
    rw [hom_of, hom_of, gen_pad]

/-- A weighted count is a model of the PROP structure when the swap has
weight `ε` with `ε + ε = 0` (Definition 26 and Remark 27). -/
def model (σ : Gate 2) (hσ : W.w2 σ + W.w2 σ = 0) : Model Gate σ where
  rel n := Con.ker (W.hom n)
  shift := fun h => by
    rw [Con.ker_rel] at h ⊢; rw [hom_shift, hom_shift, h]
  pad m := fun h => by
    rw [Con.ker_rel] at h ⊢; rw [hom_pad, hom_pad, h]
  comm1 h g := by rw [Con.ker_rel, map_mul, map_mul, mul_comm]
  comm2 h g := by rw [Con.ker_rel, map_mul, map_mul, mul_comm]
  comm3 h g := by rw [Con.ker_rel, map_mul, map_mul, mul_comm]
  scalar c := by rw [Con.ker_rel, hom_of, hom_of]; rfl
  sym s := by
    rw [Con.ker_rel]
    cases s with
    | invol =>
      rw [map_mul, hom_of, map_one, ← ofAdd_add]
      exact congrArg Multiplicative.ofAdd hσ
    | nat1 g => rw [map_mul, map_mul, mul_comm, hom_shift]; simp only [hom_of]; rfl
    | nat2 g => rw [map_mul, map_mul, mul_comm, hom_shift]; simp only [hom_of]; rfl
    | nat3 g => rw [map_mul, map_mul, mul_comm, hom_shift]; simp only [hom_of]; rfl

theorem model_rel (σ : Gate 2) (hσ : W.w2 σ + W.w2 σ = 0) {n : ℕ} (w v : Circuit Gate n) :
    (W.model σ hσ).rel n w v ↔ W.hom n w = W.hom n v := Con.ker_rel _

end Weights

/-- Lemma 25 for a weighted count: an axiom is independent when the weights
of the two sides of every other axiom on at most as many wires agree and those
of its own two sides differ. -/
theorem Weights.independent {M : Type*} [AddCommMonoid M] {P : PropPresentation Gate}
    (W : Weights Gate M) (hσ : W.w2 P.swap + W.w2 P.swap = 0) (ρ : P.Ax)
    (hS : ∀ a, P.arity a ≤ P.arity ρ → a ≠ ρ → W.hom _ (P.lhs a) = W.hom _ (P.rhs a))
    (hρ : W.hom _ (P.lhs ρ) ≠ W.hom _ (P.rhs ρ)) : P.Independent ρ :=
  P.independent_of_model (W.model P.swap hσ)
    (fun a ha hne => (W.model_rel _ hσ _ _).2 (hS a ha hne)) (fun h => hρ ((W.model_rel _ hσ _ _).1 h))

/-- `{0, 1}` under `∨` (Definition 28, `Has`): whether a gate occurs. -/
def Occ : Type := Bool

instance : DecidableEq Occ := inferInstanceAs (DecidableEq Bool)

instance : Zero Occ := ⟨false⟩

instance : Add Occ := ⟨Bool.or⟩

instance : AddCommMonoid Occ where
  add_assoc := Bool.or_assoc
  zero_add := Bool.false_or
  add_zero := Bool.or_false
  add_comm := Bool.or_comm
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

/-- The value "occurs". -/
def Occ.yes : Occ := true

theorem Occ.zero_add_zero : (0 : Occ) + 0 = 0 := rfl

/-! ### Matrix models: the structural rules -/

namespace Ops

variable {K : Type*} [CommRing K] {d : ℕ} (O : GateOps Gate K d)

theorem eval_of {n : ℕ} (g : Gen Gate n) : O.eval n (FreeMonoid.of g) = O.gen g :=
  FreeMonoid.lift_eval_of _ _

theorem eval_shift {n : ℕ} (w : Circuit Gate n) :
    O.eval (n + 1) (Circuit.shift w) = onTop 1 (O.eval n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [onTop_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, Circuit.shift_of, ih, map_mul, onTop_mul, eval_of, eval_of]
    rfl

theorem gen_pad (m : ℕ) {k : ℕ} (g : Gen Gate k) :
    O.gen (g.pad m) = onBottom (n := m) (O.gen g) := by
  induction g with
  | gate0 c =>
    show O.scalar c • (1 : Op K d _) = onBottom (O.scalar c • 1)
    rw [onBottom_smul, onBottom_one]
  | @gate1 n' c =>
    show onBottom (n := m + n') (O.gate1 c) = onBottom (n := m) (onBottom (n := n') (O.gate1 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @gate2 n' c =>
    show onBottom (n := m + n') (O.gate2 c) = onBottom (n := m) (onBottom (n := n') (O.gate2 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @gate3 n' c =>
    show onBottom (n := m + n') (O.gate3 c) = onBottom (n := m) (onBottom (n := n') (O.gate3 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @up n' g ih =>
    show onTop 1 (O.gen (g.pad m)) = onBottom (n := m) (onTop 1 (O.gen g))
    rw [ih]; exact (onBottom_onTop _).symm

theorem eval_pad (m : ℕ) {k : ℕ} (w : Circuit Gate k) :
    O.eval (m + k) (Circuit.pad m w) = onBottom (n := m) (O.eval k w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [onBottom_one]
  | mul_of g w ih =>
    rw [map_mul (Circuit.pad m), map_mul (O.eval _), ih, map_mul (O.eval k), onBottom_mul]
    congr 1
    show O.eval _ (FreeMonoid.of (g.pad m)) = _
    rw [eval_of, eval_of, gen_pad]

theorem gen_up_up {n : ℕ} (g : Gen Gate n) : O.gen g.up.up = onTop 2 (O.gen g) :=
  onTop_one_onTop (k := 1) _

theorem gen_up_up_up {n : ℕ} (g : Gen Gate n) : O.gen g.up.up.up = onTop 3 (O.gen g) := by
  show onTop 1 (O.gen g.up.up) = _
  rw [gen_up_up]; exact onTop_one_onTop (k := 2) _

theorem comm1 {n : ℕ} (h : Gate 1) (g : Gen Gate n) :
    O.eval (n + 1) (FreeMonoid.of g.up * g1 h) = O.eval (n + 1) (g1 h * FreeMonoid.of g.up) := by
  rw [map_mul, map_mul, eval_of, eval_of]
  exact (onBottom_onTop_comm (k := 1) _ _).symm

theorem comm2 {n : ℕ} (h : Gate 2) (g : Gen Gate n) :
    O.eval (n + 2) (FreeMonoid.of g.up.up * g2 h) = O.eval (n + 2) (g2 h * FreeMonoid.of g.up.up) := by
  rw [map_mul, map_mul, eval_of, eval_of, gen_up_up]
  exact (onBottom_onTop_comm (k := 2) _ _).symm

theorem comm3 {n : ℕ} (h : Gate 3) (g : Gen Gate n) :
    O.eval (n + 3) (FreeMonoid.of g.up.up.up * g3 h) =
      O.eval (n + 3) (g3 h * FreeMonoid.of g.up.up.up) := by
  rw [map_mul, map_mul, eval_of, eval_of, gen_up_up_up]
  exact (onBottom_onTop_comm (k := 3) _ _).symm

theorem scalar_up {n : ℕ} (c : Gate 0) :
    O.eval (n + 1) (FreeMonoid.of (Gen.gate0 c).up) = O.eval (n + 1) (g0 c) := by
  rw [eval_of, eval_of]
  show onTop 1 (O.scalar c • (1 : Op K d n)) = O.scalar c • 1
  rw [onTop_smul, onTop_one]

end Ops

/-! ### Projective matrix models -/

/-- Equality of matrices up to a unit scalar. -/
def ProjEq {K : Type*} [CommRing K] {ι : Type*} (A B : Matrix ι ι K) : Prop :=
  ∃ c : K, IsUnit c ∧ A = c • B

/-- The projective quotient of a matrix model (Definitions 32–34): circuits
are equal when their matrices agree up to a unit scalar.  It is a model of
the PROP structure when the laws of the symmetry hold exactly. -/
def projModel {K : Type*} [CommRing K] {d : ℕ} (O : GateOps Gate K d) (σ : Gate 2)
    (hσ : ∀ {k : ℕ} {w v : Circuit Gate k}, Sym σ k w v → O.eval k w = O.eval k v) :
    Model Gate σ where
  rel n :=
    { r := fun w v => ProjEq (O.eval n w) (O.eval n v)
      iseqv :=
        { refl := fun w => ⟨1, isUnit_one, (one_smul _ _).symm⟩
          symm := by
            rintro w v ⟨c, hc, h⟩
            obtain ⟨u, rfl⟩ := hc
            refine ⟨↑u⁻¹, Units.isUnit _, ?_⟩
            rw [h, smul_smul, Units.inv_mul, one_smul]
          trans := by
            rintro w v x ⟨c, hc, h⟩ ⟨c', hc', h'⟩
            exact ⟨c * c', hc.mul hc', by rw [h, h', smul_smul]⟩ }
      mul' := by
        rintro w v w' v' ⟨c, hc, h⟩ ⟨c', hc', h'⟩
        refine ⟨c * c', hc.mul hc', ?_⟩
        simp only [map_mul, h, h', smul_mul_smul_comm] }
  shift := by
    rintro n w v ⟨c, hc, h⟩
    exact ⟨c, hc, by simp only [Ops.eval_shift O, h, onTop_smul]⟩
  pad m k w v := by
    rintro ⟨c, hc, h⟩
    exact ⟨c, hc, by simp only [Ops.eval_pad O, h, onBottom_smul]⟩
  comm1 h g := ⟨1, isUnit_one, by rw [one_smul]; exact Ops.comm1 O h g⟩
  comm2 h g := ⟨1, isUnit_one, by rw [one_smul]; exact Ops.comm2 O h g⟩
  comm3 h g := ⟨1, isUnit_one, by rw [one_smul]; exact Ops.comm3 O h g⟩
  scalar c := ⟨1, isUnit_one, by rw [one_smul]; exact Ops.scalar_up O c⟩
  sym s := ⟨1, isUnit_one, by rw [one_smul]; exact hσ s⟩

/-- Matrices with a pair of entries whose cross ratio differs are not
proportional. -/
theorem not_projEq_of_cross {K : Type*} [CommRing K] {ι : Type*} {A B : Matrix ι ι K}
    (i j k l : ι) (h : A i j * B k l ≠ A k l * B i j) : ¬ ProjEq A B := by
  rintro ⟨c, -, rfl⟩
  apply h
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

end QCert.Minimality
