------------------------------------------------------------------------
-- Presentations of groups
--
-- A complete verification procedure: normalise, then expand what is
-- left (Amy, QPL 2018, section 4)
--
-- Section 4 of the paper observes that "the normal forms are not
-- necessarily unique and hence our reduction system is incomplete"
-- (PathSum.Examples.Incomplete and PathSum.Examples.ValidationIncomplete
-- exhibit identities whose every normal form keeps path variables), and
-- proposes a remedy: "A complete verification procedure could proceed
-- by explicitly expanding the values of remaining variables in the
-- path-sum after all possible reductions have been made, and then
-- checking equivalence to the identity transformation."  This module is
-- that procedure, for every path-sum.
--
--  * verify ξ normalises ξ with all of figure 2, at any variables, in
--    the order PathSum.Full.Match.normal-formᶠ picks (proposition 3.2:
--    it stops), and records what it reached (Verdict).  A normal form
--    without path variables is tested syntactically -- no
--    normalisation, the identity's outputs modulo 2, phase 0 modulo 1
--    (SyntacticId, PathSum.Syntactic.id⇔syntactic).  A normal form
--    that keeps path variables is expanded: every entry of its operator
--    is computed as the sum over all assignments to its remaining path
--    variables and compared with the identity's (expand, which is
--    PathSum.Brute.≋? against |x⟩ ↦ |x⟩).
--  * It is sound and complete (verdict-correct): ξ is the identity
--    exactly when what verify reached passes its test, by proposition
--    3.1 along the chain.  Hence a decision procedure (decide-id).
--  * On Clifford path-sums (internal path variables, phase of order at
--    most 2: PathSum.Full.Clifford.IsClifford) the expansion is never
--    needed.  Every rule keeps a path-sum Clifford, so a normal form
--    that keeps a path variable refutes by lemma 4.3
--    (clifford-expanded, i.e. Full.Clifford.stuck-not-id): the expansion
--    could only answer no.  verify-with takes the test of such a normal
--    form as a parameter; with the answer no (verifyᶜ, decide-idᶜ) it is
--    the procedure of corollary 4.4, complete on Clifford path-sums and
--    never expanding.  Beyond Clifford that shortcut is unsound: an
--    irreducible identity with path variables exists
--    (PathSum.Examples.ValidationIncomplete.shortcut-unsound).
--  * Footnote 2: "uniqueness would imply that equivalence checking of
--    reversible Boolean circuits is in P.  As this problem is
--    co-NP-complete, uniqueness of our normal forms would indeed imply
--    P = co-NP."  Its logical half is formalised: if equivalent normal
--    forms had as many path variables (UniqueNormalForms, the weakest
--    uniqueness up to equivalence), a normal form that keeps a path variable would never
--    be the identity, so the procedure would never need to expand
--    (unique⇒no-expansion, decide-idᵘ).  That hypothesis is false
--    (Examples.Incomplete.normal-forms-not-unique).  The
--    complexity-theoretic half -- that normalisation is polynomial,
--    that reversible-circuit equivalence is co-NP-complete, and the
--    conclusion P = co-NP -- is not formalised.
--
-- The procedure is exponential, and nothing here claims otherwise.  The
-- expansion visits 4^n entries, each a sum over 2^m′ paths of
-- polynomials evaluated over all 2^(n+m′) monomials; and the
-- normalisation itself is exponential in this formalisation, since
-- PathSum.Full.Match decides each rule's premises by comparing
-- polynomials over all their monomials (the paper's polynomial bound
-- for normalising, proposition 3.2, is not formalised).  As a decision
-- procedure it is no stronger than PathSum.Brute.≋? on ξ itself;
-- what it adds is the paper's route: reductions first, then an
-- expansion of the normal form only, over the path variables the
-- reductions could not remove (expanded-fewer), and none at all on
-- Clifford inputs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Expand (M₀ : ℕ) where

open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (zero; _+_; _≤_)
open import Data.Nat.Properties using (≤-trans; m≤n+m)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Unit.Base using (⊤)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no; does; map′)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.Brute M₀ using (≋?)
open import PathSum.Denotation M₀ using (_≋_; ≋-sym; ≋-trans)
open import PathSum.Full M using (_⟶ᶠ*_; lenᶠ; ⟶ᶠ*-length)
open import PathSum.Full.Clifford M₀ using
  (IsClifford; ⟶ᶠ*-Clifford; stuck-not-id)
open import PathSum.Full.Match M using (Irreducibleᶠ; normal-formᶠ)
open import PathSum.Full.Obstruction M using (no-paths-irreducible)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Gauss.Corollary M₀ using (syntactic?)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (μ; x[_]; 0ᴾ; _≈[_]_)
open import PathSum.Syntactic M₀ using (id⇔syntactic)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- The two tests

-- What the syntactic test asks of a path-sum without path variables.

SyntacticId : PathSum n k 0 → Set
SyntacticId {k = k} ξ =
  k ≡ 0 × (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) × phase ξ ≈[ pow M ] 0ᴾ

-- The expansion: every entry of the operator, as the sum over all
-- assignments to the path variables, against the identity's.

expand : (ξ : PathSum n k m) → Dec (ξ ≋ idPS)
expand ξ = ≋? ξ idPS

-- A reduct is the identity exactly when the path-sum is (proposition
-- 3.1 along the chain).

reduct-⇔ : {ξ : PathSum n k m} {ξ′ : PathSum n k′ m′} → ξ ⟶ᶠ* ξ′ →
           (ξ ≋ idPS ⇔ ξ′ ≋ idPS)
reduct-⇔ {ξ = ξ} {ξ′} steps = mk⇔
  (λ e → ≋-trans {ξ = ξ′} {ζ = ξ} {χ = idPS}
           (≋-sym {ξ = ξ} {ζ = ξ′} sound) e)
  (λ e → ≋-trans {ξ = ξ} {ζ = ξ′} {χ = idPS} sound e)
  where
  sound = ⟶ᶠ*-sound {ξ = ξ} {ζ = ξ′} steps


------------------------------------------------------------------------
-- The procedure

-- What normalisation reached, and the test it calls for: syntactic
-- without path variables, the expansion (or, in verify-with, whatever
-- test is supplied) with some left.

data Verdict {n k m : ℕ} (ξ : PathSum n k m) : Set where
  syntactic : ∀ {k′} (ξ′ : PathSum n k′ 0) → ξ ⟶ᶠ* ξ′ →
              Dec (SyntacticId ξ′) → Verdict ξ
  expanded  : ∀ {k′ m′} (ξ′ : PathSum n k′ (suc m′)) → ξ ⟶ᶠ* ξ′ →
              Irreducibleᶠ ξ′ → Dec (ξ′ ≋ idPS) → Verdict ξ

-- The test of a normal form that keeps path variables.

Remainder : PathSum n k m → Set
Remainder {n} ξ = ∀ {k′ m′} (ξ′ : PathSum n k′ (suc m′)) →
                  ξ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ → Dec (ξ′ ≋ idPS)

-- Normalise, then test.

verify-with : (ξ : PathSum n k m) → Remainder ξ → Verdict ξ
verify-with {n = n} ξ test = at (normal-formᶠ ξ)
  where
  at : (∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
          (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′) → Verdict ξ
  at (_ , zero  , ξ′ , steps , _)   = syntactic ξ′ steps (syntactic? ξ′)
  at (_ , suc _ , ξ′ , steps , irr) =
    expanded ξ′ steps irr (test ξ′ steps irr)

-- The paper's remedy: expand whatever is left.

verify : (ξ : PathSum n k m) → Verdict ξ
verify ξ = verify-with ξ (λ ξ′ _ _ → expand ξ′)


------------------------------------------------------------------------
-- Soundness and completeness

-- A verdict accepts when its test does.

Accepts : {ξ : PathSum n k m} → Verdict ξ → Set
Accepts (syntactic ξ′ _ _)  = SyntacticId ξ′
Accepts (expanded ξ′ _ _ _) = ξ′ ≋ idPS

accepts? : {ξ : PathSum n k m} (v : Verdict ξ) → Dec (Accepts v)
accepts? (syntactic _ _ d)  = d
accepts? (expanded _ _ _ d) = d

-- ξ is the identity exactly when its verdict accepts: a normal form
-- without path variables is the identity iff it is syntactically so,
-- and one with path variables iff its expansion says so.

verdict-correct : {ξ : PathSum n k m} (v : Verdict ξ) →
                  (ξ ≋ idPS ⇔ Accepts v)
verdict-correct {ξ = ξ} (syntactic ξ′ steps _) = mk⇔
  (λ e → Equivalence.to (id⇔syntactic ξ′)
           (Equivalence.to (reduct-⇔ {ξ = ξ} {ξ′ = ξ′} steps) e))
  (λ s → Equivalence.from (reduct-⇔ {ξ = ξ} {ξ′ = ξ′} steps)
           (Equivalence.from (id⇔syntactic ξ′) s))
verdict-correct {ξ = ξ} (expanded ξ′ steps _ _) =
  reduct-⇔ {ξ = ξ} {ξ′ = ξ′} steps

decision : {ξ : PathSum n k m} → Verdict ξ → Dec (ξ ≋ idPS)
decision v = map′ (Equivalence.from (verdict-correct v))
                  (Equivalence.to (verdict-correct v)) (accepts? v)

-- The complete procedure.

decide-id : (ξ : PathSum n k m) → Dec (ξ ≋ idPS)
decide-id ξ = decision (verify ξ)

-- The expansion runs over no more path variables than ξ has: every
-- rule removes one at least.

expanded-fewer : {ξ : PathSum n k m} {ξ′ : PathSum n k′ (suc m′)} →
                 ξ ⟶ᶠ* ξ′ → suc m′ ≤ m
expanded-fewer steps = ≤-trans (m≤n+m _ (lenᶠ steps)) (⟶ᶠ*-length steps)


------------------------------------------------------------------------
-- Clifford path-sums: the expansion is never needed

-- Every step keeps a Clifford path-sum Clifford, so an irreducible
-- reduct that keeps a path variable is not the identity (lemma 4.3):
-- the expansion could only answer no.

clifford-expanded : {ξ : PathSum n k m} → IsClifford ξ →
                    ∀ {k′ m′} (ξ′ : PathSum n k′ (suc m′)) →
                    ξ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ → ¬ (ξ′ ≋ idPS)
clifford-expanded c ξ′ steps irr =
  stuck-not-id ξ′ (⟶ᶠ*-Clifford steps c) irr

-- So on a Clifford path-sum the expanded branch never accepts.

Expanded : {ξ : PathSum n k m} → Verdict ξ → Set
Expanded (syntactic _ _ _)  = ⊥
Expanded (expanded _ _ _ _) = ⊤

clifford-rejects : {ξ : PathSum n k m} → IsClifford ξ →
                   (v : Verdict ξ) → Expanded v → ¬ Accepts v
clifford-rejects c (expanded ξ′ steps irr _) _ =
  clifford-expanded c ξ′ steps irr

-- The procedure of corollary 4.4: normalise, test syntactically, and
-- answer no, without expanding, when a path variable is left.

verifyᶜ : (ξ : PathSum n k m) → IsClifford ξ → Verdict ξ
verifyᶜ ξ c =
  verify-with ξ (λ ξ′ steps irr → no (clifford-expanded c ξ′ steps irr))

decide-idᶜ : (ξ : PathSum n k m) → IsClifford ξ → Dec (ξ ≋ idPS)
decide-idᶜ ξ c = decision (verifyᶜ ξ c)

-- It answers as the complete procedure does.

private
  does-unique : {A : Set} (d d′ : Dec A) → does d ≡ does d′
  does-unique (yes _) (yes _) = refl
  does-unique (yes a) (no ¬a) = contradiction a ¬a
  does-unique (no ¬a) (yes a) = contradiction a ¬a
  does-unique (no _)  (no _)  = refl

clifford-agrees : (ξ : PathSum n k m) (c : IsClifford ξ) →
                  does (decide-idᶜ ξ c) ≡ does (decide-id ξ)
clifford-agrees ξ c = does-unique (decide-idᶜ ξ c) (decide-id ξ)


------------------------------------------------------------------------
-- Footnote 2: what uniqueness of normal forms would give

-- The weakest uniqueness up to equivalence: equivalent irreducible
-- path-sums have as many path variables.

UniqueNormalForms : Set
UniqueNormalForms =
  ∀ {n k m k′ m′} (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
  Irreducibleᶠ ξ → Irreducibleᶠ ζ → ξ ≋ ζ → m ≡ m′

-- It would make every normal form with path variables a refutation,
-- the identity being a normal form without any ...

unique⇒no-expansion : UniqueNormalForms →
                      (ξ′ : PathSum n k (suc m)) → Irreducibleᶠ ξ′ →
                      ¬ (ξ′ ≋ idPS)
unique⇒no-expansion u ξ′ irr e =
  suc≢0 (u ξ′ idPS irr (no-paths-irreducible idPS) e)
  where
  suc≢0 : ∀ {j} → ¬ (suc j ≡ 0)
  suc≢0 ()

-- ... and so the procedure would never need to expand.

decide-idᵘ : UniqueNormalForms → (ξ : PathSum n k m) → Dec (ξ ≋ idPS)
decide-idᵘ u ξ = decision
  (verify-with ξ (λ ξ′ _ irr → no (unique⇒no-expansion u ξ′ irr)))
