/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The scalar refinement of the qutrit Clifford presentation (Appendix I)

Li, Mosca, Ross, van de Wetering and Zhao's presentation of qutrit Clifford
circuits (`QCert.QutritClifford`) has the scalar `-ω`, of order six; the
semantics of Cliff₃ has `ω₁₂ = e^{iπ/6}`, of order twelve.  Following
Appendix I, the source is refined by an order-twelve scalar: here its scalar
is replaced by `ω₁₂`, `-ω` being read as `ω₁₂¹⁰` (`ι`), and the refined rules
are the source rules read through `ι` and `ω₁₂¹² = 1` (`RRule`).

Lemma 50 (`refined_complete`): the refined presentation is complete as soon
as the source is.  A refined circuit is `ω₁₂ᵃ` times a source circuit
(`extract`, scalars being central), so two refined circuits with the same
matrix give `ζᵃ M = ζᵇ M'` for source matrices `M`, `M'`.  The hypothesis
"no hidden phases" of Lemma 50 is proved here, not assumed: the matrices of
source circuits have their entries in `ℚ(ω)` (`QEven`, no odd power of
`ζ = ω₁₂`), so `a ≡ b (mod 2)`, `ζ^{b-a}` is a power of `-ω`, and the source's
completeness applies.
-/
import QCert.Minimality.QutritClifford.Semantics
import QCert.Minimality.Cross
import QCert.Minimality.Comm
import QCert.QutritClifford.Semantics
import QCert.QutritClifford.Soundness
import Mathlib.NumberTheory.Real.Irrational

namespace QCert.Minimality.QutritClifford

open QCert.Circuit

/-! ### The refined source -/

/-- Li et al.'s gates with the scalar `-ω` replaced by `ω₁₂`. -/
inductive RGate : ℕ → Type
  /-- The scalar `ω₁₂`. -/
  | w : RGate 0
  | H : RGate 1
  | S : RGate 1
  | CZ : RGate 2
  deriving DecidableEq

theorem rhsc : ∀ c c' : RGate 0, c = c' := by intro c c'; cases c; cases c'; rfl

/-- The source read in the refined gates: `-ω ↦ ω₁₂¹⁰`. -/
def ι : GateSubst QCert.QutritClifford.Gate RGate where
  φ0 _ := g0 RGate.w ^ 10
  φ1
    | .H => g1 RGate.H
    | .S => g1 RGate.S
  φ2
    | .CZ => g2 RGate.CZ
  φ3 g := nomatch g

/-- The refined rules: the source rules read through `ι`, and `ω₁₂¹² = 1`. -/
inductive RRule : CRel RGate
  | src {k : ℕ} {w v : Circuit QCert.QutritClifford.Gate k} (r : QCert.QutritClifford.Rule k w v) :
      RRule k (ι.map k w) (ι.map k v)
  | w12 : RRule 0 (g0 RGate.w ^ 12) 1

/-- The refined theory. -/
abbrev RTh : CRel RGate := Lift (Padded RRule)

/-! ### Semantics -/

theorem ζ_eq : QCert.QutritClifford.ζ = ZZeta.ζ12 := by
  apply Complex.ext <;> simp [QCert.QutritClifford.ζ, ZZeta.ζ12]

theorem ζ_pow_ten : ZZeta.ζ12 ^ 10 = -QCert.QutritClifford.ωℂ := by
  rw [QCert.QutritClifford.ωℂ_eq, ← ζ_eq]
  have h3 := QCert.QutritClifford.ζ_pow_three
  have h4 := QCert.QutritClifford.ζ_pow_four
  have : QCert.QutritClifford.ζ ^ 10 = (QCert.QutritClifford.ζ ^ 3) ^ 2 * QCert.QutritClifford.ζ ^ 4 := by
    ring
  rw [this, h3, h4, Complex.I_sq]; ring

/-- The refined semantics: `ω₁₂ ↦ e^{iπ/6}`, the other gates as the source's. -/
noncomputable def RS : GateSem RGate ℂ 3 where
  scalar
    | .w => ⟨ZZeta.ζ12, Qutrit.ζ12_mem⟩
  gate1
    | .H => QCert.QutritClifford.gateSem.gate1 .H
    | .S => QCert.QutritClifford.gateSem.gate1 .S
  gate2
    | .CZ => QCert.QutritClifford.gateSem.gate2 .CZ
  gate3 g := nomatch g

theorem RS_scalar_pow {n : ℕ} (a : ℕ) :
    (RS.sem n (g0 RGate.w ^ a) : Op ℂ 3 n) = ZZeta.ζ12 ^ a • 1 := by
  rw [GateSem.sem_val, map_pow]
  have : RS.toOps.eval n (g0 RGate.w) = ZZeta.ζ12 • (1 : Op ℂ 3 n) := FreeMonoid.lift_eval_of _ _
  rw [this, smul_pow, one_pow]

/-- The source read through `ι` keeps its matrices. -/
theorem sem_ι {n : ℕ} (c : Circuit QCert.QutritClifford.Gate n) :
    RS.sem n (ι.map n c) = QCert.QutritClifford.gateSem.sem n c := by
  refine ι.sem_map QCert.QutritClifford.gateSem RS (fun g => ?_) (fun g => ?_) (fun g => ?_)
    (fun g => nomatch g) c
  · cases g
    apply Subtype.ext
    rw [show ι.φ0 QCert.QutritClifford.Gate.negω = g0 RGate.w ^ 10 from rfl, RS_scalar_pow,
      ζ_pow_ten]
    rfl
  · cases g <;> rfl
  · cases g; rfl

/-! ### Scalars come out in front -/

theorem scalar_pow_comm {n : ℕ} (a : ℕ) (u : Circuit RGate n) :
    Derivable (RTh n) (g0 RGate.w ^ a * u) (u * g0 RGate.w ^ a) := by
  have h1 : Derivable (RTh n) (g0 RGate.w * u) (u * g0 RGate.w) := by
    refine comm_words rhsc _ _ fun x hx y _ => ?_
    have : x = Gen.gate0 RGate.w := by simpa using hx
    subst this
    simp [Gen.apart, Gen.span]
  induction a with
  | zero => simp only [pow_zero, one_mul, mul_one]; exact Derivable.refl _
  | succ a ih =>
    rw [pow_succ', mul_assoc]
    refine ((Derivable.refl _).mul ih).trans ?_
    rw [← mul_assoc]
    refine (h1.mul (Derivable.refl _)).trans ?_
    rw [mul_assoc, ← pow_succ']

theorem gen_extract : ∀ {n : ℕ} (x : Gen RGate n), ∃ (a : ℕ) (c : Circuit QCert.QutritClifford.Gate n),
    Derivable (RTh n) (FreeMonoid.of x) (g0 RGate.w ^ a * ι.map n c)
  | _, .gate0 .w => ⟨1, 1, by simp only [pow_one, map_one, mul_one]; exact Derivable.refl _⟩
  | _, .gate1 .H => ⟨0, FreeMonoid.of (Gen.gate1 QCert.QutritClifford.Gate.H), by
      rw [pow_zero, one_mul, ι.map_of]; rfl⟩
  | _, .gate1 .S => ⟨0, FreeMonoid.of (Gen.gate1 QCert.QutritClifford.Gate.S), by
      rw [pow_zero, one_mul, ι.map_of]; rfl⟩
  | _, .gate2 .CZ => ⟨0, FreeMonoid.of (Gen.gate2 QCert.QutritClifford.Gate.CZ), by
      rw [pow_zero, one_mul, ι.map_of]; rfl⟩
  | _, .gate3 g => nomatch g
  | _, @Gen.up _ m y => by
    obtain ⟨a, c, h⟩ := gen_extract y
    refine ⟨a, shift c, ?_⟩
    have h1 := derivable_shift (R := Padded RRule) h
    rw [Circuit.shift_of, map_mul, map_pow, ← ι.map_shift] at h1
    refine h1.trans (Derivable.mul ?_ (Derivable.refl _))
    have hs : Derivable (RTh (m + 1)) (shift (g0 RGate.w)) (g0 RGate.w) :=
      Derivable.of (Lift.scalar RGate.w)
    clear h1 h
    induction a with
    | zero => simp only [pow_zero]; exact Derivable.refl _
    | succ a ih => rw [pow_succ, pow_succ]; exact ih.mul hs

/-- Every refined circuit is a power of `ω₁₂` times a source circuit. -/
theorem extract {n : ℕ} (w : Circuit RGate n) :
    ∃ (a : ℕ) (c : Circuit QCert.QutritClifford.Gate n),
      Derivable (RTh n) w (g0 RGate.w ^ a * ι.map n c) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨0, 1, by simp only [pow_zero, map_one, mul_one]; exact Derivable.refl _⟩
  | mul_of x w ih =>
    obtain ⟨a, c, h⟩ := ih
    obtain ⟨a', c', h'⟩ := gen_extract x
    refine ⟨a' + a, c' * c, ?_⟩
    have e1 := h'.mul h
    refine e1.trans ?_
    rw [map_mul, pow_add]
    have e2 : Derivable (RTh n) (ι.map n c' * g0 RGate.w ^ a) (g0 RGate.w ^ a * ι.map n c') :=
      (scalar_pow_comm a _).symm
    have e3 := (Derivable.refl (g0 RGate.w ^ a')).mul (e2.mul (Derivable.refl (ι.map n c)))
    simpa only [mul_assoc] using e3

/-! ### Moving source derivations, and `ω₁₂¹² = 1` -/

theorem Gen.pad_zero_heq {G : ℕ → Type} {k : ℕ} (g : Gen G k) : HEq (g.pad 0) g := by
  induction g with
  | @gate0 n c => exact heq_index (Nat.zero_add n) (fun t => (Gen.gate0 c : Gen G t))
  | @gate1 n c => exact heq_index (Nat.zero_add n) (fun t => (Gen.gate1 c : Gen G (t + 1)))
  | @gate2 n c => exact heq_index (Nat.zero_add n) (fun t => (Gen.gate2 c : Gen G (t + 2)))
  | @gate3 n c => exact heq_index (Nat.zero_add n) (fun t => (Gen.gate3 c : Gen G (t + 3)))
  | @up n g ih => exact heq_up (Nat.zero_add n) ih

theorem pad_zero_heq {G : ℕ → Type} {k : ℕ} (w : Circuit G k) : HEq (Circuit.pad 0 w) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact heq_index (Nat.zero_add k) (fun t => (1 : Circuit G t))
  | mul_of g w ih =>
    rw [map_mul]
    exact heq_mul (Nat.zero_add k) (heq_of (Nat.zero_add k) (Gen.pad_zero_heq g)) ih

/-- A rule on its own wires is a derivable equation there. -/
theorem rule_derivable {G : ℕ → Type} {R : CRel G} {k : ℕ} {w v : Circuit G k} (r : R k w v) :
    Derivable (Lift (Padded R) k) w v :=
  Derivable.of (lift_cast (Nat.zero_add k) (pad_zero_heq w) (pad_zero_heq v)
    (Lift.rule (Padded.pad 0 r)))

/-- Source derivations hold in the refined theory. -/
theorem ι_derivable {n : ℕ} {c c' : Circuit QCert.QutritClifford.Gate n}
    (h : Derivable (QCert.QutritClifford.Theory n) c c') :
    Derivable (RTh n) (ι.map n c) (ι.map n c') :=
  ι.derivable_map rhsc (fun _ _ _ r => rule_derivable (RRule.src r)) h

theorem w12_at {n : ℕ} : Derivable (RTh n) (g0 RGate.w ^ 12) 1 := by
  have := derivable_pad n (rule_derivable (R := RRule) RRule.w12)
  simpa [map_pow] using this

theorem w_pow_mod {n : ℕ} (a : ℕ) :
    Derivable (RTh n) (g0 RGate.w ^ a) (g0 RGate.w ^ (a % 12)) := by
  conv_lhs => rw [← Nat.mod_add_div a 12, pow_add, pow_mul]
  have h : Derivable (RTh n) ((g0 RGate.w ^ 12) ^ (a / 12)) 1 := by
    induction a / 12 with
    | zero => simp only [pow_zero]; exact Derivable.refl _
    | succ j ih => rw [pow_succ]; simpa using ih.mul w12_at
  simpa using (Derivable.refl (g0 RGate.w ^ (a % 12))).mul h

theorem ι_negω_pow {n : ℕ} (t : ℕ) :
    ι.map n (g0 QCert.QutritClifford.Gate.negω ^ t) = g0 RGate.w ^ (10 * t) := by
  rw [map_pow, pow_mul]
  rfl

/-! ### No hidden phases: the source's matrices have entries in `ℚ(ω)` -/

/-- An element of `ℚ(ζ)` without odd powers of `ζ`, i.e. in `ℚ(ω)`. -/
abbrev QEven (x : QCert.QutritClifford.Q) : Prop := x.a1 = 0 ∧ x.a3 = 0

/-- An element of `ℚ(ζ)` with only odd powers of `ζ`. -/
abbrev QOdd (x : QCert.QutritClifford.Q) : Prop := x.a0 = 0 ∧ x.a2 = 0

theorem QEven.zero : QEven 0 := ⟨rfl, rfl⟩

theorem QEven.add {x y : QCert.QutritClifford.Q} (hx : QEven x) (hy : QEven y) :
    QEven (x + y) := by
  obtain ⟨h1, h3⟩ := hx; obtain ⟨k1, k3⟩ := hy
  exact ⟨by simp [h1, k1], by simp [h3, k3]⟩

theorem QEven.mul {x y : QCert.QutritClifford.Q} (hx : QEven x) (hy : QEven y) :
    QEven (x * y) := by
  obtain ⟨h1, h3⟩ := hx; obtain ⟨k1, k3⟩ := hy
  exact ⟨by simp [h1, h3, k1, k3], by simp [h1, h3, k1, k3]⟩

theorem QOdd.mul_even {x y : QCert.QutritClifford.Q} (hx : QOdd x) (hy : QEven y) :
    QOdd (x * y) := by
  obtain ⟨h0, h2⟩ := hx; obtain ⟨k1, k3⟩ := hy
  exact ⟨by simp [h0, h2, k1, k3], by simp [h0, h2, k1, k3]⟩

theorem eq_zero_of_even_odd {x : QCert.QutritClifford.Q} (he : QEven x) (ho : QOdd x) : x = 0 :=
  Quartic.ext ho.1 he.1 ho.2 he.2

theorem QEven.sum {α : Type*} (s : Finset α) (f : α → QCert.QutritClifford.Q)
    (h : ∀ i ∈ s, QEven (f i)) : QEven (∑ i ∈ s, f i) :=
  Finset.sum_induction f QEven (fun _ _ => QEven.add) QEven.zero h

/-- A matrix with entries in `ℚ(ω)`. -/
def MEven {n : ℕ} (M : Op QCert.QutritClifford.Q 3 n) : Prop := ∀ s t, QEven (M s t)

theorem MEven.mul {n : ℕ} {A B : Op QCert.QutritClifford.Q 3 n} (hA : MEven A) (hB : MEven B) :
    MEven (A * B) := fun s t => by
  rw [Matrix.mul_apply]; exact QEven.sum _ _ fun u _ => (hA s u).mul (hB u t)

theorem MEven.one {n : ℕ} : MEven (1 : Op QCert.QutritClifford.Q 3 n) := fun s t => by
  by_cases h : s = t
  · subst h; rw [Matrix.one_apply_eq]; exact ⟨rfl, rfl⟩
  · rw [Matrix.one_apply_ne h]; exact QEven.zero

theorem MEven.onBottom {n k : ℕ} {G : Op QCert.QutritClifford.Q 3 k} (hG : MEven G) :
    MEven (onBottom (n := n) G) := fun s t => by
  rw [onBottom_apply]; split_ifs
  · exact hG _ _
  · exact QEven.zero

theorem MEven.onTop {n k : ℕ} {M : Op QCert.QutritClifford.Q 3 n} (hM : MEven M) :
    MEven (onTop k M) := fun s t => by
  rw [onTop_apply]; split_ifs
  · exact hM _ _
  · exact QEven.zero

theorem MEven.ofMat {k : ℕ} {M : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) QCert.QutritClifford.Q}
    (h : ∀ i j, QEven (M i j)) : MEven (ofMat M) := fun _ _ => h _ _

theorem HQ_even : ∀ i j, QEven (QCert.QutritClifford.HQ i j) := by decide +kernel
theorem SQ_even : ∀ i j, QEven (QCert.QutritClifford.SQ i j) := by decide +kernel
theorem CZQ_even : ∀ i j, QEven (QCert.QutritClifford.CZQ i j) := by decide +kernel

theorem gen_even : ∀ {n : ℕ} (g : Gen QCert.QutritClifford.Gate n),
    MEven (QCert.QutritClifford.ops.gen g)
  | _, .gate0 .negω => fun s t => by
    show QEven ((QCert.QutritClifford.negωQ • (1 : Op QCert.QutritClifford.Q 3 _)) s t)
    rw [Matrix.smul_apply, smul_eq_mul]; exact QEven.mul ⟨rfl, rfl⟩ (MEven.one s t)
  | _, .gate1 .H => MEven.onBottom (MEven.ofMat HQ_even)
  | _, .gate1 .S => MEven.onBottom (MEven.ofMat SQ_even)
  | _, .gate2 .CZ => MEven.onBottom (MEven.ofMat CZQ_even)
  | _, .gate3 g => nomatch g
  | _, .up g => MEven.onTop (gen_even g)

theorem eval_even {n : ℕ} (c : Circuit QCert.QutritClifford.Gate n) :
    MEven (QCert.QutritClifford.ops.eval n c) := by
  induction c using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact MEven.one
  | mul_of g w ih =>
    rw [map_mul, show QCert.QutritClifford.ops.eval n (FreeMonoid.of g) =
      QCert.QutritClifford.ops.gen g from FreeMonoid.lift_eval_of _ _]
    exact (gen_even g).mul ih

theorem src_sem_eq {n : ℕ} (c : Circuit QCert.QutritClifford.Gate n) :
    (QCert.QutritClifford.gateSem.sem n c : Op ℂ 3 n) =
      (QCert.QutritClifford.ops.eval n c).map QCert.QutritClifford.toC := by
  rw [GateSem.sem_val, QCert.QutritClifford.toOps_eq, GateOps.eval_map]

theorem irrational_sqrt3 : Irrational (Real.sqrt 3) := by
  have := irrational_sqrt_natCast_iff.mpr (show ¬ IsSquare (3 : ℕ) by decide +kernel)
  simpa using this

theorem rat_sqrt3_eq_zero {q r : ℚ} (h : (q : ℝ) + r * Real.sqrt 3 = 0) : q = 0 ∧ r = 0 := by
  by_cases hr : r = 0
  · subst hr; simp at h; exact ⟨h, rfl⟩
  · exfalso
    apply irrational_sqrt3
    refine ⟨-q / r, ?_⟩
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    push_cast
    field_simp
    linarith

/-- `ℚ(ζ)` inside `ℂ`: the reading is injective. -/
theorem toC_injective : Function.Injective QCert.QutritClifford.toC := by
  intro x y hxy
  have hz : QCert.QutritClifford.toC (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [← sub_eq_zero]
  generalize x - y = z at hz
  rw [QCert.QutritClifford.toC_apply, QCert.QutritClifford.ζ_sq, QCert.QutritClifford.ζ_pow_three]
    at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [QCert.QutritClifford.ζ] at hre him
  have h1 := rat_sqrt3_eq_zero (q := z.a0 + z.a2 / 2) (r := z.a1 / 2) (by push_cast; linarith)
  have h2 := rat_sqrt3_eq_zero (q := z.a1 / 2 + z.a3) (r := z.a2 / 2) (by push_cast; linarith)
  apply Quartic.ext <;> simp <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Lemma 50 -/

/-- The refined rules are sound. -/
theorem RS_sound {n : ℕ} {x y : Circuit RGate n} (h : Derivable (RTh n) x y) :
    RS.sem n x = RS.sem n y := by
  refine derivable_sound (fun w w' r => ?_) h
  refine RS.lift_sound (RS.padded_sound fun k w v r => ?_) _ w w' r
  cases r with
  | src r => rw [sem_ι, sem_ι, QCert.QutritClifford.rule_sound r]
  | w12 =>
    apply Subtype.ext
    rw [RS_scalar_pow, map_one, OneMemClass.coe_one]
    rw [show ZZeta.ζ12 ^ 12 = (ZZeta.ζ12 ^ 3) ^ 4 by ring, ZZeta.ζ12_pow_three, Complex.I_pow_four,
      one_smul]

theorem RS_form {n : ℕ} (a : ℕ) (c : Circuit QCert.QutritClifford.Gate n) :
    (RS.sem n (g0 RGate.w ^ a * ι.map n c) : Op ℂ 3 n) =
      ZZeta.ζ12 ^ a • (QCert.QutritClifford.gateSem.sem n c : Op ℂ 3 n) := by
  rw [map_mul, Submonoid.coe_mul, RS_scalar_pow, sem_ι, smul_mul_assoc, one_mul]

/-- `ζ` in `ℚ(ζ)`. -/
abbrev Xq : QCert.QutritClifford.Q := Quartic.X

theorem toC_Xq : QCert.QutritClifford.toC Xq = ZZeta.ζ12 := by
  rw [← ζ_eq]; exact Quartic.lift_X _ _

theorem Xq_pow_twelve : Xq ^ 12 = 1 := by decide +kernel

theorem Xq_pow_odd : ∀ r < 12, r % 2 = 1 → QOdd (Xq ^ r) := by decide +kernel

/-- No hidden phases: `ζᵃ A = ζᵇ B` for nonzero matrices over `ℚ(ω)` forces
`a ≡ b (mod 2)`. -/
theorem parity {n : ℕ} {a b : ℕ} {A B : Op QCert.QutritClifford.Q 3 n} (hA : MEven A)
    (hB : MEven B) (hB0 : B ≠ 0)
    (h : ZZeta.ζ12 ^ a • A.map QCert.QutritClifford.toC =
      ZZeta.ζ12 ^ b • B.map QCert.QutritClifford.toC) :
    a % 2 = b % 2 := by
  obtain ⟨s, t, hst⟩ : ∃ s t, B s t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hB0 (Matrix.ext hc)
  have hq : Xq ^ a * A s t = Xq ^ b * B s t := by
    apply toC_injective
    have := congrFun (congrFun h s) t
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    rw [map_mul, map_mul, map_pow, map_pow, toC_Xq]
    exact this
  have h2 : Xq ^ ((a + 11 * b) % 12) * A s t = B s t := by
    have e1 : Xq ^ (a + 11 * b) = Xq ^ ((a + 11 * b) % 12) := by
      conv_lhs => rw [← Nat.mod_add_div (a + 11 * b) 12, pow_add, pow_mul, Xq_pow_twelve, one_pow,
        mul_one]
    have e2 : Xq ^ (11 * b) * Xq ^ b = 1 := by
      rw [← pow_add, show 11 * b + b = 12 * b by ring, pow_mul, Xq_pow_twelve, one_pow]
    calc Xq ^ ((a + 11 * b) % 12) * A s t = Xq ^ (11 * b) * (Xq ^ a * A s t) := by
          rw [← e1, pow_add]; ring
      _ = Xq ^ (11 * b) * (Xq ^ b * B s t) := by rw [hq]
      _ = B s t := by rw [← mul_assoc, e2, one_mul]
  by_contra hne
  have hodd : (a + 11 * b) % 12 % 2 = 1 := by omega
  have ho := (Xq_pow_odd _ (Nat.mod_lt _ (by norm_num)) hodd).mul_even (hA s t)
  rw [h2] at ho
  exact hst (eq_zero_of_even_odd (hB s t) ho)

theorem src_ne_zero {n : ℕ} (c : Circuit QCert.QutritClifford.Gate n) :
    QCert.QutritClifford.ops.eval n c ≠ 0 := by
  intro h0
  have hu := (QCert.QutritClifford.gateSem.sem n c).2
  rw [Matrix.mem_unitaryGroup_iff, src_sem_eq, h0] at hu
  have : (1 : Op ℂ 3 n) = 0 := by
    rw [← hu, Matrix.map_zero _ (map_zero _), zero_mul]
  have hne : (1 : Op ℂ 3 n) ≠ 0 := one_ne_zero
  exact hne this

theorem ζ12_ne_zero : ZZeta.ζ12 ≠ 0 := by
  intro h
  have := ZZeta.ζ12_pow_three
  rw [h, zero_pow (by norm_num)] at this
  exact Complex.I_ne_zero this.symm

theorem ζ12_pow_mod (k : ℕ) : ZZeta.ζ12 ^ k = ZZeta.ζ12 ^ (k % 12) := by
  conv_lhs => rw [← Nat.mod_add_div k 12, pow_add, pow_mul]
  rw [show ZZeta.ζ12 ^ 12 = (ZZeta.ζ12 ^ 3) ^ 4 by ring, ZZeta.ζ12_pow_three, Complex.I_pow_four,
    one_pow, mul_one]

/-- One direction of Lemma 50's argument: `a ≤ b`. -/
theorem refined_step
    (hsrc : ∀ n (w v : Circuit QCert.QutritClifford.Gate n),
      QCert.QutritClifford.gateSem.sem n w = QCert.QutritClifford.gateSem.sem n v →
        Derivable (QCert.QutritClifford.Theory n) w v)
    {n : ℕ} {a b : ℕ} (hab : a ≤ b) (hb : b < 12) (c c' : Circuit QCert.QutritClifford.Gate n)
    (h : RS.sem n (g0 RGate.w ^ a * ι.map n c) = RS.sem n (g0 RGate.w ^ b * ι.map n c')) :
    Derivable (RTh n) (g0 RGate.w ^ a * ι.map n c) (g0 RGate.w ^ b * ι.map n c') := by
  have hm0 := congrArg (fun U : Matrix.unitaryGroup (State 3 n) ℂ => (U : Op ℂ 3 n)) h
  simp only [RS_form] at hm0
  have hm := hm0
  rw [src_sem_eq, src_sem_eq] at hm
  have hpar := parity (eval_even c) (eval_even c') (src_ne_zero c') hm
  obtain ⟨j, hj⟩ : ∃ j, b = a + 2 * j := ⟨(b - a) / 2, by omega⟩
  set t := 5 * j % 6 with ht
  have h10 : (a + 10 * t) % 12 = b := by omega
  have hζ : ZZeta.ζ12 ^ (10 * t) = ZZeta.ζ12 ^ (2 * j) := by
    rw [ζ12_pow_mod (10 * t), ζ12_pow_mod (2 * j)]
    congr 1
    omega
  -- the source circuits differ by `(-ω)ᵗ`
  have hsem : QCert.QutritClifford.gateSem.sem n c =
      QCert.QutritClifford.gateSem.sem n (g0 QCert.QutritClifford.Gate.negω ^ t * c') := by
    apply Subtype.ext
    have hM : (QCert.QutritClifford.gateSem.sem n c : Op ℂ 3 n) =
        ZZeta.ζ12 ^ (2 * j) • (QCert.QutritClifford.gateSem.sem n c' : Op ℂ 3 n) := by
      apply smul_right_injective _ (pow_ne_zero a ζ12_ne_zero)
      simp only
      rw [smul_smul, ← pow_add, ← hj]
      exact hm0
    rw [hM, ← hζ, map_mul, Submonoid.coe_mul, map_pow, SubmonoidClass.coe_pow]
    have hneg : (QCert.QutritClifford.gateSem.sem n (g0 QCert.QutritClifford.Gate.negω) : Op ℂ 3 n) =
        (-QCert.QutritClifford.ωℂ) • 1 := rfl
    rw [hneg, smul_pow, one_pow, smul_mul_assoc, one_mul, ← ζ_pow_ten, ← pow_mul]
  have hd := ι_derivable (hsrc n _ _ hsem)
  rw [map_mul, ι_negω_pow] at hd
  have e1 := (Derivable.refl (g0 RGate.w ^ a)).mul hd
  rw [← mul_assoc, ← pow_add] at e1
  refine e1.trans ?_
  have e2 := (w_pow_mod (n := n) (a + 10 * t)).mul (Derivable.refl (ι.map n c'))
  rwa [h10] at e2

/-- Lemma 50 for the qutrit Clifford presentation: the refined presentation
is complete as soon as the source is. -/
theorem refined_complete
    (hsrc : ∀ n (w v : Circuit QCert.QutritClifford.Gate n),
      QCert.QutritClifford.gateSem.sem n w = QCert.QutritClifford.gateSem.sem n v →
        Derivable (QCert.QutritClifford.Theory n) w v)
    {n : ℕ} {w v : Circuit RGate n} (h : RS.sem n w = RS.sem n v) : Derivable (RTh n) w v := by
  obtain ⟨a, c, hw⟩ := extract w
  obtain ⟨b, c', hv⟩ := extract v
  have hw' := hw.trans ((w_pow_mod a).mul (Derivable.refl (ι.map n c)))
  have hv' := hv.trans ((w_pow_mod b).mul (Derivable.refl (ι.map n c')))
  have hs : RS.sem n (g0 RGate.w ^ (a % 12) * ι.map n c) =
      RS.sem n (g0 RGate.w ^ (b % 12) * ι.map n c') := by
    rw [← RS_sound hw', ← RS_sound hv', h]
  refine hw'.trans (Derivable.trans ?_ hv'.symm)
  rcases le_total (a % 12) (b % 12) with hab | hab
  · exact refined_step hsrc hab (Nat.mod_lt _ (by norm_num)) c c' hs
  · exact (refined_step hsrc hab (Nat.mod_lt _ (by norm_num)) c' c hs.symm).symm

end QCert.Minimality.QutritClifford
