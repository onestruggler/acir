/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# PROP presentations of circuit fragments, independence and minimality

Blake, *Simpler presentations for many fragments of quantum circuits*
(FSCD 2026, arXiv:2602.09874), works in PROPs: the swap is structural and
the PROP coherence laws (Figure 1) hold in every presented PROP.  The
framework's circuits (`QCert.Circuit`) form a PRO whose structural rules
(`QCert.Lift`: shifting an equation up, gates on disjoint wires commute, a
scalar is the same on every wire) give the interchange law.  To obtain the
PROP we add the basic swap `σ` as a two-wire gate together with the laws of
the symmetry (`Sym`): `σ ∘ σ = id` (Figure 1, involution) and the naturality
of the block swap `σₙ` (Figure 1, naturality) for every generator, including
`σ` itself (the Yang–Baxter equation).  Naturality for an arbitrary circuit
follows from naturality for the generators, so `Lift (Padded (Base P S))`
is the congruence of the presented PROP `P/S` of Definition 5.

A presentation (`PropPresentation`) is a gate set with a designated swap and
an indexed family of axioms, each an equation between circuits on its own
`arity` wires.  `P.Derives S n w v` says that `w = v` on `n` wires follows
from the axioms selected by `S` together with the PROP structure.  On this we
define Definition 23 (`Independent`), Definition 24 (`MinimalUpTo`), the
completeness of Definition 9 (`Complete`, `CompleteUpTo`) and prove

* Remark 14 / the remark before Definition 24 (`derives_truncate`): a
  derivation on `n` wires uses only axioms of arity at most `n`;
* Lemma 25 (`independent_of_model`): an axiom is independent if some model
  of the PROP structure satisfies the other axioms but not it.

Circuits are words in operator order (`w * v` applies `v` first); the
paper's diagrams are read left to right, which `seq` records: `seq [c₁, …, cₖ]`
applies `c₁` first.
-/
import QCert.Circuit.Semantics

namespace QCert.Minimality

open Circuit

variable {Gate : ℕ → Type}

/-! ### Circuits in diagram order -/

/-- A circuit drawn left to right: `seq [c₁, c₂, …, cₖ]` applies `c₁` first,
so as a word in operator order it is `cₖ * ⋯ * c₂ * c₁`. -/
def seq {n : ℕ} : List (Circuit Gate n) → Circuit Gate n
  | [] => 1
  | c :: l => seq l * c

@[simp] theorem seq_nil {n : ℕ} : seq ([] : List (Circuit Gate n)) = 1 := rfl
@[simp] theorem seq_cons {n : ℕ} (c : Circuit Gate n) (l : List (Circuit Gate n)) :
    seq (c :: l) = seq l * c := rfl

theorem seq_append {n : ℕ} (l l' : List (Circuit Gate n)) :
    seq (l ++ l') = seq l' * seq l := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih, mul_assoc]

/-! ### The symmetry -/

/-- The cycle `σ₂ = (σ ⊗ id) ∘ (id ⊗ σ)` on three wires carrying wire `0` to
wire `2` and wires `1, 2` down to `0, 1` (operator order: the swap of wires
`0, 1` first). -/
def cyc2 (σ : Gate 2) : Circuit Gate 3 := shift (g2 σ) * g2 σ

/-- The cycle `σ₃` on four wires carrying wire `0` to wire `3`. -/
def cyc3 (σ : Gate 2) : Circuit Gate 4 := shift (shift (g2 σ)) * shift (g2 σ) * g2 σ

/-- The laws of the symmetry of a PROP whose basic swap is the two-wire gate
`σ` (Figure 1): the involution `σ ∘ σ = id₂` and the naturality
`σₘ ∘ (f ⊗ id₁) = (id₁ ⊗ f) ∘ σₙ` for every generator `f` on one, two or three
wires (the block swap `σₙ` carries the bottom wire, wire `0`, over the `n`
wires of `f`).  For `f = σ` naturality is the Yang–Baxter equation.  For a
scalar `σ₀ = id` and naturality is the structural rule `Lift.scalar`. -/
inductive Sym (σ : Gate 2) : CRel Gate
  /-- `σ ∘ σ = id₂`. -/
  | invol : Sym σ 2 (g2 σ * g2 σ) 1
  /-- Naturality for a one-wire gate `g`: `σ ∘ (g ⊗ id₁) = (id₁ ⊗ g) ∘ σ`. -/
  | nat1 (g : Gate 1) : Sym σ 2 (g2 σ * shift (g1 g)) (g1 g * g2 σ)
  /-- Naturality for a two-wire gate `g`: `σ₂ ∘ (g ⊗ id₁) = (id₁ ⊗ g) ∘ σ₂`. -/
  | nat2 (g : Gate 2) : Sym σ 3 (cyc2 σ * shift (g2 g)) (g2 g * cyc2 σ)
  /-- Naturality for a three-wire gate `g`: `σ₃ ∘ (g ⊗ id₁) = (id₁ ⊗ g) ∘ σ₃`. -/
  | nat3 (g : Gate 3) : Sym σ 4 (cyc3 σ * shift (g3 g)) (g3 g * cyc3 σ)

/-! ### Presentations -/

/-- A presentation of a PROP of circuits (Definitions 3–5): a gate set with a
designated basic swap, and a family of axioms, each an equation between two
circuits on its own `arity` wires. -/
structure PropPresentation (Gate : ℕ → Type) where
  /-- The basic swap `σ = σ₁,₁`, a structural morphism of the PROP. -/
  swap : Gate 2
  /-- The names of the axioms. -/
  Ax : Type
  /-- The number of wires an axiom is drawn on. -/
  arity : Ax → ℕ
  /-- The left-hand side of an axiom. -/
  lhs : (a : Ax) → Circuit Gate (arity a)
  /-- The right-hand side of an axiom. -/
  rhs : (a : Ax) → Circuit Gate (arity a)

namespace PropPresentation

variable (P : PropPresentation Gate)

/-- The relations on their own wires: the laws of the symmetry and the axioms
selected by `S`. -/
inductive Base (S : P.Ax → Prop) : CRel Gate
  | sym {k : ℕ} {w v : Circuit Gate k} : Sym P.swap k w v → Base S k w v
  | ax (a : P.Ax) : S a → Base S (P.arity a) (P.lhs a) (P.rhs a)

/-- `P.Derives S n w v`: the equation `w = v` between `n`-wire circuits holds
in the PROP presented by the axioms selected by `S` (Definition 5): it
follows from those axioms and the PROP structure. -/
def Derives (S : P.Ax → Prop) (n : ℕ) (w v : Circuit Gate n) : Prop :=
  QCert.Derives (Padded (P.Base S)) n w v

/-- Derivability from all the axioms. -/
abbrev Proves (n : ℕ) (w v : Circuit Gate n) : Prop := P.Derives (fun _ => True) n w v

/-- Definition 23: the axiom `ρ` is independent of the other axioms (within
the selection `S`): its two sides are not equal in the PROP presented by the
other selected axioms. -/
def IndependentIn (S : P.Ax → Prop) (ρ : P.Ax) : Prop :=
  ¬ P.Derives (fun a => S a ∧ a ≠ ρ) (P.arity ρ) (P.lhs ρ) (P.rhs ρ)

/-- Definition 23: `ρ` is independent of the other axioms. -/
def Independent (ρ : P.Ax) : Prop := P.IndependentIn (fun _ => True) ρ

/-- Definition 23: the rule set is minimal, every axiom being independent. -/
def Minimal : Prop := ∀ ρ, P.Independent ρ

/-- Definition 24: the axioms on at most `k` wires. -/
def UpTo (k : ℕ) (a : P.Ax) : Prop := P.arity a ≤ k

/-- Definition 24: the rule set is minimal up to `k` wires: every axiom on at
most `k` wires is independent of the other axioms on at most `k` wires. -/
def MinimalUpTo (k : ℕ) : Prop := ∀ ρ, P.arity ρ ≤ k → P.IndependentIn (P.UpTo k) ρ

/-! #### Truncation (Remark 14) -/

theorem derivable_mono {n : ℕ} {R R' : WRel (Gen Gate n)} (h : ∀ w v, R w v → R' w v)
    {w v : Circuit Gate n} (d : Derivable R w v) : Derivable R' w v :=
  Con.conGen_mono h d

private theorem lift_mono {S S' : P.Ax → Prop} (h : ∀ a, S a → S' a) {n : ℕ}
    {w v : Circuit Gate n} (r : Lift (Padded (P.Base S)) n w v) :
    Lift (Padded (P.Base S')) n w v := by
  induction r with
  | rule r =>
    cases r with
    | pad m b =>
      refine Lift.rule (Padded.pad m ?_)
      cases b with
      | sym s => exact Base.sym s
      | ax a ha => exact Base.ax a (h a ha)
  | shift _ ih => exact Lift.shift ih
  | comm1 c g => exact Lift.comm1 c g
  | comm2 c g => exact Lift.comm2 c g
  | comm3 c g => exact Lift.comm3 c g
  | scalar c => exact Lift.scalar c

theorem derives_mono {S S' : P.Ax → Prop} (h : ∀ a, S a → S' a) {n : ℕ}
    {w v : Circuit Gate n} (d : P.Derives S n w v) : P.Derives S' n w v :=
  derivable_mono (fun _ _ r => P.lift_mono h r) d

private theorem lift_truncate {S : P.Ax → Prop} {n : ℕ} {w v : Circuit Gate n}
    (r : Lift (Padded (P.Base S)) n w v) :
    ∀ k, n ≤ k → Lift (Padded (P.Base (fun a => S a ∧ P.arity a ≤ k))) n w v := by
  induction r with
  | rule r =>
    intro k hk
    cases r with
    | @pad j m w v b =>
      refine Lift.rule (Padded.pad m ?_)
      cases b with
      | sym s => exact Base.sym s
      | ax a ha => exact Base.ax a ⟨ha, by omega⟩
  | shift _ ih => intro k hk; exact Lift.shift (ih k (by omega))
  | comm1 c g => intro _ _; exact Lift.comm1 c g
  | comm2 c g => intro _ _; exact Lift.comm2 c g
  | comm3 c g => intro _ _; exact Lift.comm3 c g
  | scalar c => intro _ _; exact Lift.scalar c

/-- Remark 14 and the remark before Definition 24: every generator has as
many inputs as outputs, so a derivation of an equation on `n` wires only uses
axioms on at most `n` wires. -/
theorem derives_truncate {S : P.Ax → Prop} {n : ℕ} {w v : Circuit Gate n}
    (d : P.Derives S n w v) : P.Derives (fun a => S a ∧ P.arity a ≤ n) n w v :=
  derivable_mono (fun _ _ r => P.lift_truncate r n le_rfl) d

/-- Independence is unchanged by adding or removing axioms on more wires than
the axiom tested: independence within the axioms on at most `k ≥ arity ρ`
wires is independence within all axioms. -/
theorem independentIn_upTo_iff {k : ℕ} {ρ : P.Ax} (hk : P.arity ρ ≤ k) :
    P.IndependentIn (P.UpTo k) ρ ↔ P.Independent ρ := by
  constructor
  · intro h d
    apply h
    refine P.derives_mono ?_ (P.derives_truncate d)
    rintro a ⟨⟨-, ha⟩, hle⟩
    exact ⟨le_trans hle hk, ha⟩
  · intro h d
    exact h (P.derives_mono (fun a ha => ⟨trivial, ha.2⟩) d)

/-- Minimality up to `k` wires says exactly that every axiom on at most `k`
wires is independent. -/
theorem minimalUpTo_iff {k : ℕ} :
    P.MinimalUpTo k ↔ ∀ ρ, P.arity ρ ≤ k → P.Independent ρ :=
  forall_congr' fun _ => imp_congr_right fun hk => P.independentIn_upTo_iff hk

/-! #### Completeness (Definition 9) -/

/-- Definition 9: the presentation is complete for the semantics `sem` (one
monoid homomorphism per number of wires): circuits with the same
interpretation are equal in the presented PROP. -/
def Complete {M : ℕ → Type*} [∀ n, Monoid (M n)] (sem : ∀ n, Circuit Gate n →* M n) : Prop :=
  ∀ n (w v : Circuit Gate n), sem n w = sem n v → P.Proves n w v

/-- Definition 9: completeness up to `k` wires. -/
def CompleteUpTo {M : ℕ → Type*} [∀ n, Monoid (M n)] (sem : ∀ n, Circuit Gate n →* M n)
    (k : ℕ) : Prop :=
  ∀ n, n ≤ k → ∀ (w v : Circuit Gate n), sem n w = sem n v → P.Proves n w v

end PropPresentation

/-! ### Models (Lemma 25) -/

/-- A model of the PROP structure: a congruence on the circuits of each width
that is preserved by moving a circuit up one wire or putting it on the bottom
wires of a wider circuit, and that contains the structural rules and the
laws of the symmetry.  Such a congruence is the kernel of a PROP morphism out
of the free PROP, and conversely. -/
structure Model (Gate : ℕ → Type) (σ : Gate 2) where
  /-- The equality of the model, on `n`-wire circuits. -/
  rel : (n : ℕ) → Con (Circuit Gate n)
  shift {n : ℕ} {w v : Circuit Gate n} : rel n w v → rel (n + 1) (shift w) (shift v)
  pad (m : ℕ) {k : ℕ} {w v : Circuit Gate k} : rel k w v → rel (m + k) (Circuit.pad m w) (Circuit.pad m v)
  comm1 {n : ℕ} (h : Gate 1) (g : Gen Gate n) :
    rel (n + 1) (FreeMonoid.of g.up * g1 h) (g1 h * FreeMonoid.of g.up)
  comm2 {n : ℕ} (h : Gate 2) (g : Gen Gate n) :
    rel (n + 2) (FreeMonoid.of g.up.up * g2 h) (g2 h * FreeMonoid.of g.up.up)
  comm3 {n : ℕ} (h : Gate 3) (g : Gen Gate n) :
    rel (n + 3) (FreeMonoid.of g.up.up.up * g3 h) (g3 h * FreeMonoid.of g.up.up.up)
  scalar {n : ℕ} (c : Gate 0) : rel (n + 1) (FreeMonoid.of (Gen.gate0 c).up) (g0 c)
  sym {k : ℕ} {w v : Circuit Gate k} : Sym σ k w v → rel k w v

namespace Model

variable {σ : Gate 2} (M : Model Gate σ)

/-- A model satisfying the selected axioms satisfies every equation derived
from them. -/
theorem sound {P : PropPresentation Gate} (hσ : P.swap = σ) {S : P.Ax → Prop}
    (hS : ∀ a, S a → M.rel (P.arity a) (P.lhs a) (P.rhs a))
    {n : ℕ} {w v : Circuit Gate n} (d : P.Derives S n w v) : M.rel n w v := by
  have key : ∀ n (w v : Circuit Gate n), Lift (Padded (P.Base S)) n w v → M.rel n w v := by
    intro n w v r
    induction r with
    | rule r =>
      cases r with
      | pad m b =>
        apply M.pad m
        cases b with
        | sym s => exact M.sym (hσ ▸ s)
        | ax a ha => exact hS a ha
    | shift _ ih => exact M.shift ih
    | comm1 c g => exact M.comm1 c g
    | comm2 c g => exact M.comm2 c g
    | comm3 c g => exact M.comm3 c g
    | scalar c => exact M.scalar c
  exact Con.conGen_le (fun x y r => key n x y r) d

end Model

/-- Lemma 25: if a model of the PROP structure satisfies every selected axiom
other than `ρ` but not `ρ`, then `ρ` is independent of the other selected
axioms. -/
theorem PropPresentation.independentIn_of_model {P : PropPresentation Gate} {S : P.Ax → Prop}
    {ρ : P.Ax} (M : Model Gate P.swap)
    (hS : ∀ a, S a → a ≠ ρ → M.rel (P.arity a) (P.lhs a) (P.rhs a))
    (hρ : ¬ M.rel (P.arity ρ) (P.lhs ρ) (P.rhs ρ)) : P.IndependentIn S ρ :=
  fun d => hρ (M.sound rfl (fun a ha => hS a ha.1 ha.2) d)

/-- Lemma 25 with the truncation of Remark 14: to show `ρ` independent it
suffices that the model satisfies the other axioms on at most as many wires
as `ρ`. -/
theorem PropPresentation.independent_of_model {P : PropPresentation Gate} {ρ : P.Ax}
    (M : Model Gate P.swap)
    (hS : ∀ a, P.arity a ≤ P.arity ρ → a ≠ ρ → M.rel (P.arity a) (P.lhs a) (P.rhs a))
    (hρ : ¬ M.rel (P.arity ρ) (P.lhs ρ) (P.rhs ρ)) : P.Independent ρ :=
  (P.independentIn_upTo_iff le_rfl).1 (P.independentIn_of_model M hS hρ)

end QCert.Minimality
