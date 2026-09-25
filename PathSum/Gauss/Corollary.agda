------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.4 for Clifford circuits over {H, CNOT, R_k}, by Gaussian
-- elimination (Amy, QPL 2018)
--
-- The paper proves corollary 4.4 like this.  ⟦C⟧ is well-formed, so
-- by lemma 4.1 it suffices to check ⟦C⟧|f(x,y)=x ≡ |x⟩ ↦ |x⟩.  "As
-- f(x,y) is linear, we can compute via Gaussian elimination a solution
-- y so that f(x,y) = x for any x -- if no such solution exists,
-- ⟦C⟧ ≢ |x⟩ ↦ |x⟩."  Each substitution keeps the order of the phase at
-- most 2.  So by lemma 4.3 and proposition 3.2 the restriction either
-- reduces to |x⟩ ↦ |x⟩ or is not the identity.  This module is that
-- proof, for the paper's own gate set: circuits over
-- {H, CNOT, R_k, R_k†} (PathSum.CRK.Circuit) of level at most 2, the
-- Clifford ones.  The only phase gates such a circuit can contain are
-- R_0 = I, R_1 = Z and R_2 = S, and their inverses.  PathSum.CRK.Compile
-- reaches the same characterisation by another route: it compiles the
-- circuit to {H, S, CZ} and reduces the restriction of the compiled
-- circuit.  Here the reduction runs on the restriction of ⟦ C ⟧
-- itself, reified by PathSum.Gauss, as in the paper.
--
-- The plan:
--
--  1. ⟦ C ⟧ᴿ is ⟦C⟧|f(x,y)=x as elimination reifies it.  It is partial:
--     restriction (gauss (stateᶜ C)) is nothing when the elimination
--     refutes, and just (m′ , ξ) otherwise, where ξ is PathSum.Gauss's
--     ξᴿ at the circuit's normalisation.  The generic facts about a
--     run of elimination come first (restriction-nothing,
--     restriction-just, restriction-identity), stated for any state
--     with linear outputs; the circuit facts are these at stateᶜ C,
--     the state whose path-sum ⟦ C ⟧ is by definition.
--  2. No solution: refuted-gauss exhibits an input whose diagonal entry
--     of ⟦ C ⟧ vanishes, so ⟦ C ⟧ is not the identity (not-id-gauss).
--     This is the paper's "if no such solution exists".
--  3. A solution: ξ has only internal path variables, the identity's
--     outputs and the diagonal of ⟦ C ⟧.  Its phase has order at most
--     max(2, level C) (proposition 2.14, corrected, then lemma 2.13 at
--     every substitution).  Elimination removed at most n path
--     variables to get it.  And, by lemma 4.1, ⟦ C ⟧ is the identity
--     exactly when ξ is (lemma-4-1-gauss).  None of this needs the
--     circuit to be Clifford.
--  4. For level C ≤ 2 the phase of ξ has order at most 2, so lemma 4.3
--     (progress-gauss, lemma-4-3-gauss) and its iteration
--     (PathSum.Clifford.corollary-4-4) apply to ξ.  This gives
--     corollary-4-4-⟦⟧-gauss: the circuit is refuted, either by the
--     elimination or by the reduction, or a chain of reductions from ξ
--     ends without path variables, at a path-sum that is the identity
--     exactly when ⟦ C ⟧ is.
--  5. The end, read syntactically (PathSum.Syntactic).  For every chain
--     from ξ that ends without path variables, ⟦ C ⟧ is the identity
--     exactly when the end has no normalisation, the identity's outputs
--     modulo 2 and phase 0 modulo 2^M (corollary-4-4-any-gauss).  This
--     holds at every level, and for chains of the rules at any path
--     variable too (corollary-4-4-anyᵍ-gauss).  For Clifford circuits:
--     ⟦ C ⟧ is the identity iff the elimination does not refute and
--     some chain from ξ ends at a syntactic identity
--     (corollary-4-4-gauss).  Equivalently, iff the elimination does
--     not refute, some chain ends without path variables, and every
--     such chain ends at a syntactic identity
--     (corollary-4-4-every-gauss).  The existence of a chain is needed
--     there: when the circuit is not the identity the reduction can get
--     stuck, and "every chain" would then hold vacuously.  Lemma 4.3
--     supplies the chain for the identities: they are never refuted
--     (identity-reifies), and their restriction always reduces to a
--     syntactic identity (identity-reduces).  Along any elimination
--     strategy of PathSum.Anywhere.Clifford: corollary-4-4-by-gauss.
--  6. The decision (decidable-gauss) runs this route for every Clifford
--     circuit.  It eliminates; it reduces by lemma 4.3 until no path
--     variable is left; and it tests the end coefficient by coefficient
--     (syntactic?, with PathSum.Anywhere.Match's _≈?[_]_).
--     Decidability as such is elementary, since the matrix has finitely
--     many entries (PathSum.CRK.Theorems.circuit-decidable is a search),
--     and the type Dec (⟦ C ⟧ ≋ idPS) does not record the route.
--
-- Departures.  The gate set carries R_k† as definition 2.9 does, and
-- "Clifford" is read as level C ≤ 2.  The order bound on the phase is
-- max(2, level C), not the level, as proposition 2.14 has to be
-- corrected (PathSum.CRK.Circuit).  The restriction is the one
-- PathSum.Gauss computes, with its own choice of pivots and with the
-- identity's outputs in place of the solved forms.  The reduction
-- applies the rules at the first path variable, as PathSum.Clifford
-- does; the rules at any path variable enter through
-- corollary-4-4-anyᵍ-gauss and corollary-4-4-by-gauss.  Proposition 3.2
-- is not needed for termination here: every rule removes a path
-- variable.
--
-- Not formalised: the polynomial time bound, the whole point of the
-- corollary.  This covers the running time of the elimination,
-- proposition 3.2's bounds on the reduction, and the space-time volume
-- of a circuit.  Polynomials here are functions on all 2^(n+m)
-- monomials, and the final syntactic test inspects every one of them,
-- so the procedure as formalised is exponential.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Gauss.Corollary (M₀ : ℕ) where

open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (+_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (suc; _≤_; _⊔_; _+_)
open import Data.Product.Base using (_×_; _,_; ∃; Σ; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary.Decidable using (Dec; no; map′; _×?_)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (_⟶ᵍ*_)
open import PathSum.Anywhere.Match M using (_≈?[_]_)
open import PathSum.Anywhere.Sound M₀ using (⟶ᵍ*-sound)
open import PathSum.Base using (PathSum; phase; out; idPS; Internal)
open import PathSum.CRK.Amp M₀ using (toPS; ampᴸ)
open import PathSum.CRK.Circuit M using
  (State; poly; Circuit; norm; level; paths; run; init; ⟦_⟧; prop-2-14;
   prop-2-14-k)
open import PathSum.Cyclotomic M₀ using (0ᴬ; _≐_)
open import PathSum.Denotation M₀ using (amp; _≋_; semantics)
open import PathSum.Gauss M₀ using
  (Gauss; refuted; reduced; Reified; gauss; ξᴿ; amp-toPS; refute;
   reified-Internal; reified-out; reified-Ord≤; reified-diag;
   reified-≋; reified-removes)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.Order M using (Ord≤; pow)
open import PathSum.Polynomial using (μ; x[_]; 0ᴾ; _≈[_]_)
open import PathSum.Reduction M using (_⟶_; _⟶*_)

import Data.Nat.Properties as ℕ
import PathSum.Anywhere.Clifford
import PathSum.Clifford
import PathSum.CRK.Semantics
import PathSum.Denotation
import PathSum.Syntactic

private
  module AC    = PathSum.Anywhere.Clifford M₀
  module Cliff = PathSum.Clifford M₀ semantics
  module Den   = PathSum.Denotation M₀
  module Sem   = PathSum.CRK.Semantics M₀
  module Syn   = PathSum.Syntactic M₀

  variable
    n m k k′ m′ m″ : ℕ


------------------------------------------------------------------------
-- The restriction a run of elimination reifies

-- Nothing when the run refutes; otherwise the reified restriction ξᴿ,
-- at whatever normalisation k the path-sum has.

restriction : {st : State n m} → Gauss st → Maybe (Σ ℕ (PathSum n k))
restriction (refuted _ _)       = nothing
restriction {k = k} (reduced r) = just (Reified.m′ r , ξᴿ r {k = k})

-- What the reified restriction ξ of st satisfies: only internal path
-- variables, the identity's outputs, a phase of no higher order than
-- that of st, and the diagonal of st.  By lemma 4.1 it is the identity
-- exactly when st is, provided st is well-formed.  Elimination
-- removed at most n path variables to reach it.

record Reifies {n m k m′ : ℕ} (st : State n m) (ξ : PathSum n k m′) :
               Set where
  field
    internal : Internal ξ
    outputs  : ∀ w → out ξ w ≡ μ x[ w ]
    order    : ∀ {d} → Ord≤ d (poly st) → Ord≤ d (phase ξ)
    diagonal : ∀ x → amp (toPS {k = k} st) x x ≐ amp ξ x x
    identity : WellFormed (toPS {k = k} st) →
               (toPS {k = k} st ≋ idPS ⇔ ξ ≋ idPS)
    removes  : m ≤ m′ + n

-- A refuting run exhibits an input whose diagonal entry vanishes.

restriction-nothing : {st : State n m} (g : Gauss st) →
                      restriction {k = k} g ≡ nothing →
                      ∃ λ x → ampᴸ st x x ≐ 0ᴬ
restriction-nothing (refuted x z) _  = x , z
restriction-nothing (reduced r)   ()

-- What a reifying run returns satisfies Reifies.

restriction-just : {st : State n m} (g : Gauss st)
                   {ξ : PathSum n k m′} →
                   restriction g ≡ just (m′ , ξ) → Reifies st ξ
restriction-just (refuted _ _) ()
restriction-just {k = k} (reduced r) refl = record
  { internal = reified-Internal r {k = k}
  ; outputs  = reified-out r {k = k}
  ; order    = λ {d} → reified-Ord≤ r {d = d} {k = k}
  ; diagonal = reified-diag r {k = k}
  ; identity = reified-≋ r {k = k}
  ; removes  = reified-removes r
  }

-- An identity is never refuted: a refuting run exhibits a vanishing
-- diagonal entry, and no diagonal entry of the identity is 0.

restriction-identity : {st : State n m} (g : Gauss st) →
                       toPS {k = k} st ≋ idPS →
                       ∃ λ m′ → ∃ λ (ξ : PathSum n k m′) →
                         restriction g ≡ just (m′ , ξ)
restriction-identity {k = k} {st = st} (refuted x z) eq =
  contradiction eq (refute {k = k} st x z)
restriction-identity (reduced r) _ = _ , _ , refl


------------------------------------------------------------------------
-- The circuit's restriction

-- The state a circuit runs to.  ⟦ C ⟧ is toPS of it, by definition
-- (PathSum.Gauss.⟦⟧-state).

stateᶜ : (C : Circuit n) → State n (paths C)
stateᶜ C = proj₂ (run C init)

-- ⟦C⟧|f(x,y)=x, reified by Gaussian elimination -- or nothing, when
-- elimination refutes.

⟦_⟧ᴿ : (C : Circuit n) → Maybe (Σ ℕ (PathSum n (norm C)))
⟦ C ⟧ᴿ = restriction (gauss (stateᶜ C))

private
  WellFormed-⟦⟧ : (C : Circuit n) → WellFormed ⟦ C ⟧
  WellFormed-⟦⟧ C x = ≤-reflexive (Sem.⟦⟧-unit-columns C x)


------------------------------------------------------------------------
-- No solution: the circuit is refuted

-- "If no such solution exists, ⟦C⟧ ≢ |x⟩ ↦ |x⟩": elimination exhibits
-- an input whose diagonal entry vanishes.

refuted-gauss : (C : Circuit n) → ⟦ C ⟧ᴿ ≡ nothing →
                ∃ λ x → amp ⟦ C ⟧ x x ≐ 0ᴬ
refuted-gauss C eq =
  at (restriction-nothing {k = norm C} (gauss (stateᶜ C)) eq)
  where
  at : (∃ λ x → ampᴸ (stateᶜ C) x x ≐ 0ᴬ) → ∃ λ x → amp ⟦ C ⟧ x x ≐ 0ᴬ
  at (x , z) =
    x , λ i → trans (amp-toPS {k = norm C} (stateᶜ C) x x i) (z i)

not-id-gauss : (C : Circuit n) → ⟦ C ⟧ᴿ ≡ nothing → ¬ (⟦ C ⟧ ≋ idPS)
not-id-gauss C eq =
  at (restriction-nothing {k = norm C} (gauss (stateᶜ C)) eq)
  where
  at : (∃ λ x → ampᴸ (stateᶜ C) x x ≐ 0ᴬ) → ¬ (⟦ C ⟧ ≋ idPS)
  at (x , z) = refute {k = norm C} (stateᶜ C) x z


------------------------------------------------------------------------
-- A solution: the reified restriction

module _ {n : ℕ} (C : Circuit n) {m′ : ℕ} {ξ : PathSum n (norm C) m′}
         (eq : ⟦ C ⟧ᴿ ≡ just (m′ , ξ)) where

  private
    R : Reifies (stateᶜ C) ξ
    R = restriction-just (gauss (stateᶜ C)) eq

  -- Only internal path variables, and the identity's outputs.

  ⟦⟧ᴿ-Internal : Internal ξ
  ⟦⟧ᴿ-Internal = Reifies.internal R

  ⟦⟧ᴿ-out : ∀ w → out ξ w ≡ μ x[ w ]
  ⟦⟧ᴿ-out = Reifies.outputs R

  -- The diagonal of ⟦ C ⟧: ξ is its isometry restriction.

  ⟦⟧ᴿ-diagonal : ∀ x → amp ⟦ C ⟧ x x ≐ amp ξ x x
  ⟦⟧ᴿ-diagonal = Reifies.diagonal R

  -- "ord(P[y_i ← f_i]) ≤ ord(P) ≤ 2": the bound of proposition 2.14,
  -- which is 2 for a Clifford circuit.

  ⟦⟧ᴿ-Ord≤ : Ord≤ (2 ⊔ level C) (phase ξ)
  ⟦⟧ᴿ-Ord≤ = Reifies.order R {2 ⊔ level C} (prop-2-14 C)

  ⟦⟧ᴿ-Ord≤2 : level C ≤ 2 → Ord≤ 2 (phase ξ)
  ⟦⟧ᴿ-Ord≤2 lv = Reifies.order R {2} (prop-2-14-k 2 ℕ.≤-refl C lv)

  -- Section 4.1's "removing up to n path variables".

  ⟦⟧ᴿ-removes : paths C ≤ m′ + n
  ⟦⟧ᴿ-removes = Reifies.removes R

  -- Lemma 4.1: ⟦ C ⟧ is the identity exactly when its restriction is.

  lemma-4-1-gauss : ⟦ C ⟧ ≋ idPS ⇔ ξ ≋ idPS
  lemma-4-1-gauss = Reifies.identity R (WellFormed-⟦⟧ C)


------------------------------------------------------------------------
-- A verdict on the restriction, carried back to the circuit

-- Whatever is equivalent to the reified restriction -- a reduct, by
-- proposition 3.1 -- is the identity exactly when the circuit is.

reduct≋-gauss : (C : Circuit n) {ξ : PathSum n (norm C) m′} →
                ⟦ C ⟧ᴿ ≡ just (m′ , ξ) →
                {ξ′ : PathSum n k′ m″} → ξ ≋ ξ′ →
                (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
reduct≋-gauss C {ξ} eq {ξ′} eqR = mk⇔
  (λ e → Den.≋-trans {ξ = ξ′} {ζ = ξ} {χ = idPS}
           (Den.≋-sym {ξ = ξ} {ζ = ξ′} eqR)
           (Equivalence.to (lemma-4-1-gauss C eq) e))
  (λ e → Equivalence.from (lemma-4-1-gauss C eq)
           (Den.≋-trans {ξ = ξ} {ζ = ξ′} {χ = idPS} eqR e))

-- Without path variables left, being the identity is syntactic
-- (PathSum.Syntactic).

syntactic-gauss : (C : Circuit n) {ξ : PathSum n (norm C) m′} →
  ⟦ C ⟧ᴿ ≡ just (m′ , ξ) → {ξ′ : PathSum n k′ 0} → ξ ≋ ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
syntactic-gauss C eq {ξ′} eqR = mk⇔
  (λ e → Equivalence.to (Syn.id⇔syntactic ξ′)
           (Equivalence.to (reduct≋-gauss C eq {ξ′ = ξ′} eqR) e))
  (λ s → Equivalence.from (reduct≋-gauss C eq {ξ′ = ξ′} eqR)
           (Equivalence.from (Syn.id⇔syntactic ξ′) s))

-- The syntactic test is decidable, coefficient by coefficient.

syntactic? : (ξ′ : PathSum n k′ 0) →
  Dec (k′ ≡ 0 ×
       (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
syntactic? {k′ = k′} ξ′ =
  (k′ ℕ.≟ 0) ×?
  (all? (λ w → out ξ′ w ≈?[ + 2 ] μ x[ w ]) ×?
   (phase ξ′ ≈?[ pow M ] 0ᴾ))


------------------------------------------------------------------------
-- Lemma 4.3 at the restriction of a Clifford circuit

-- Progress: a rule applies to the restriction, keeping its path
-- variables internal and its phase of order at most 2, or the
-- restriction is not the identity.

progress-gauss : (C : Circuit n) → level C ≤ 2 →
                 {ξ : PathSum n (norm C) (suc m′)} →
                 ⟦ C ⟧ᴿ ≡ just (suc m′ , ξ) → Cliff.Progress ξ
progress-gauss C lv {ξ} eq =
  Cliff.progress ξ (⟦⟧ᴿ-Internal C eq) (⟦⟧ᴿ-Ord≤2 C eq lv)

-- Lemma 4.3 as the paper states it, for an identity circuit: some rule
-- applies, and the reduct is again a restriction of the same kind.

lemma-4-3-gauss : (C : Circuit n) → level C ≤ 2 →
                  {ξ : PathSum n (norm C) (suc m′)} →
                  ⟦ C ⟧ᴿ ≡ just (suc m′ , ξ) → ⟦ C ⟧ ≋ idPS →
                  ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ m′) →
                    (ξ ⟶ ξ′) × Internal ξ′ × Ord≤ 2 (phase ξ′)
lemma-4-3-gauss {n = n} {m′ = m′} C lv {ξ} eq C≋id =
  go (progress-gauss C lv eq)
  where
  go : Cliff.Progress ξ →
       ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ m′) →
         (ξ ⟶ ξ′) × Internal ξ′ × Ord≤ 2 (phase ξ′)
  go (Cliff.reduces ξ′ step int′ ord′) = _ , ξ′ , step , int′ , ord′
  go (Cliff.not-id ¬id)                =
    contradiction (Equivalence.to (lemma-4-1-gauss C eq) C≋id) ¬id


------------------------------------------------------------------------
-- Corollary 4.4

-- The elimination refutes, or the reduction of the restriction
-- refutes, or it ends without path variables at a path-sum that is the
-- identity exactly when the circuit is.

private
  Verdict : Circuit n → Set
  Verdict {n} C =
    (∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) → ⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
       ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
         (ξ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
    ⊎ ¬ (⟦ C ⟧ ≋ idPS)

corollary-4-4-⟦⟧-gauss : (C : Circuit n) → level C ≤ 2 →
  (∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) → ⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
       (ξ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C ⟧ ≋ idPS)
corollary-4-4-⟦⟧-gauss {n = n} C lv = by ⟦ C ⟧ᴿ refl
  where
  by : (r : Maybe (Σ ℕ (PathSum n (norm C)))) → ⟦ C ⟧ᴿ ≡ r → Verdict C
  by nothing          eq = inj₂ (not-id-gauss C eq)
  by (just (m′ , ξ))  eq =
    reduce (Cliff.corollary-4-4 ξ (⟦⟧ᴿ-Internal C eq) (⟦⟧ᴿ-Ord≤2 C eq lv))
    where
    reduce : Cliff.Reduces ξ → Verdict C
    reduce (Cliff.done {ξ′ = ξ′} steps) = inj₁
      (m′ , ξ , eq , _ , ξ′ , steps ,
       reduct≋-gauss C eq {ξ′ = ξ′} (Cliff.⟶*-sound steps))
    reduce (Cliff.no-id ¬id) =
      inj₂ (λ e → ¬id (Equivalence.to (lemma-4-1-gauss C eq) e))

-- Whatever chain from the restriction ends without path variables, the
-- circuit is the identity exactly when that end is syntactically
-- |x⟩ ↦ |x⟩.  This needs no bound on the level.

corollary-4-4-any-gauss : (C : Circuit n) {ξ : PathSum n (norm C) m′} →
  ⟦ C ⟧ᴿ ≡ just (m′ , ξ) → {ξ′ : PathSum n k′ 0} → ξ ⟶* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-any-gauss C eq {ξ′} steps =
  syntactic-gauss C eq {ξ′ = ξ′} (Cliff.⟶*-sound steps)

-- The same for chains of the rules at any path variable.

corollary-4-4-anyᵍ-gauss : (C : Circuit n) {ξ : PathSum n (norm C) m′} →
  ⟦ C ⟧ᴿ ≡ just (m′ , ξ) → {ξ′ : PathSum n k′ 0} → ξ ⟶ᵍ* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-anyᵍ-gauss C eq {ξ′} steps =
  syntactic-gauss C eq {ξ′ = ξ′} (⟶ᵍ*-sound steps)

-- An identity circuit is never refuted by the elimination ...

identity-reifies : (C : Circuit n) → ⟦ C ⟧ ≋ idPS →
                   ∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) →
                     ⟦ C ⟧ᴿ ≡ just (m′ , ξ)
identity-reifies C C≋id =
  restriction-identity {k = norm C} (gauss (stateᶜ C)) C≋id

-- ... and, if it is Clifford, lemma 4.3 reduces its restriction to a
-- syntactic identity.

identity-reduces : (C : Circuit n) → level C ≤ 2 →
  {ξ : PathSum n (norm C) m′} → ⟦ C ⟧ᴿ ≡ just (m′ , ξ) → ⟦ C ⟧ ≋ idPS →
  ∃ λ (ξ′ : PathSum n 0 0) → (ξ ⟶* ξ′) ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ
identity-reduces {n = n} C lv {ξ} eq C≋id =
  by (Cliff.corollary-4-4 ξ (⟦⟧ᴿ-Internal C eq) (⟦⟧ᴿ-Ord≤2 C eq lv))
  where
  Ends : Set
  Ends = ∃ λ (ξ′ : PathSum n 0 0) → (ξ ⟶* ξ′) ×
           (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ

  end : ∀ {k′} (ξ′ : PathSum n k′ 0) → ξ ⟶* ξ′ →
        k′ ≡ 0 × (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) ×
        phase ξ′ ≈[ pow M ] 0ᴾ → Ends
  end ξ′ steps (refl , outs , ph) = ξ′ , steps , outs , ph

  by : Cliff.Reduces ξ → Ends
  by (Cliff.done {ξ′ = ξ′} steps) = end ξ′ steps
    (Equivalence.to (corollary-4-4-any-gauss C eq {ξ′ = ξ′} steps) C≋id)
  by (Cliff.no-id ¬id) =
    contradiction (Equivalence.to (lemma-4-1-gauss C eq) C≋id) ¬id

-- A Clifford circuit is the identity exactly when the elimination does
-- not refute and some chain from its restriction ends at a syntactic
-- identity.

corollary-4-4-gauss : (C : Circuit n) → level C ≤ 2 →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) → ⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ (ξ′ : PathSum n 0 0) → (ξ ⟶* ξ′) ×
       (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-gauss {n = n} C lv = mk⇔ to from
  where
  Some : Set
  Some = ∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) →
           ⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
           ∃ λ (ξ′ : PathSum n 0 0) → (ξ ⟶* ξ′) ×
             (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ

  to : ⟦ C ⟧ ≋ idPS → Some
  to C≋id = reduce (identity-reifies C C≋id)
    where
    reduce : (∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) →
                ⟦ C ⟧ᴿ ≡ just (m′ , ξ)) → Some
    reduce (m′ , ξ , eq) = m′ , ξ , eq , identity-reduces C lv eq C≋id

  from : Some → ⟦ C ⟧ ≋ idPS
  from (m′ , ξ , eq , ξ′ , steps , outs , ph) =
    Equivalence.from (corollary-4-4-any-gauss C eq {ξ′ = ξ′} steps)
                     (refl , outs , ph)

-- Equivalently: the elimination does not refute, some chain from the
-- restriction ends without path variables, and every such chain ends
-- at a syntactic identity.

corollary-4-4-every-gauss : (C : Circuit n) → level C ≤ 2 →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) → ⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
     (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → ξ ⟶* ξ′) ×
     (∀ {k′} {ξ′ : PathSum n k′ 0} → ξ ⟶* ξ′ →
        k′ ≡ 0 × (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) ×
        phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-every-gauss {n = n} C lv = mk⇔ to from
  where
  Every : Set
  Every = ∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) →
            ⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
            (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → ξ ⟶* ξ′) ×
            (∀ {k′} {ξ′ : PathSum n k′ 0} → ξ ⟶* ξ′ →
               k′ ≡ 0 × (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) ×
               phase ξ′ ≈[ pow M ] 0ᴾ)

  to : ⟦ C ⟧ ≋ idPS → Every
  to C≋id = reduce (identity-reifies C C≋id)
    where
    reduce : (∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) →
                ⟦ C ⟧ᴿ ≡ just (m′ , ξ)) → Every
    reduce (m′ , ξ , eq) =
      m′ , ξ , eq , (0 , proj₁ chain , proj₁ (proj₂ chain)) ,
      (λ {k′} {ξ′} steps →
         Equivalence.to (corollary-4-4-any-gauss C eq {ξ′ = ξ′} steps)
                        C≋id)
      where
      chain = identity-reduces C lv eq C≋id

  from : Every → ⟦ C ⟧ ≋ idPS
  from (m′ , ξ , eq , (k′ , ξ′ , steps) , every) =
    Equivalence.from (corollary-4-4-any-gauss C eq {ξ′ = ξ′} steps)
                     (every steps)

-- Along any elimination strategy (PathSum.Anywhere.Clifford): the
-- circuit is refuted, or the strategy's chain from the restriction ends
-- without path variables, at a path-sum whose syntax decides the
-- circuit.

private
  VerdictBy : AC.Strategy n → Circuit n → Set
  VerdictBy {n} choose C =
    (∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) → ⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
       ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → AC.Follows choose ξ ξ′ ×
         (⟦ C ⟧ ≋ idPS ⇔
          (k′ ≡ 0 ×
           (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)))
    ⊎ ¬ (⟦ C ⟧ ≋ idPS)

corollary-4-4-by-gauss : (choose : AC.Strategy n) (C : Circuit n) →
  level C ≤ 2 →
  (∃ λ m′ → ∃ λ (ξ : PathSum n (norm C) m′) → ⟦ C ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → AC.Follows choose ξ ξ′ ×
       (⟦ C ⟧ ≋ idPS ⇔
        (k′ ≡ 0 ×
         (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)))
  ⊎ ¬ (⟦ C ⟧ ≋ idPS)
corollary-4-4-by-gauss {n = n} choose C lv = by ⟦ C ⟧ᴿ refl
  where
  by : (r : Maybe (Σ ℕ (PathSum n (norm C)))) → ⟦ C ⟧ᴿ ≡ r →
       VerdictBy choose C
  by nothing          eq = inj₂ (not-id-gauss C eq)
  by (just (m′ , ξ))  eq = reduce
    (AC.corollary-4-4-by choose ξ (⟦⟧ᴿ-Internal C eq) (⟦⟧ᴿ-Ord≤2 C eq lv))
    where
    reduce : AC.ReducesBy choose ξ → VerdictBy choose C
    reduce (AC.done {ξ′ = ξ′} f) = inj₁
      (m′ , ξ , eq , _ , ξ′ , f ,
       corollary-4-4-anyᵍ-gauss C eq {ξ′ = ξ′} (AC.Follows⇒⟶ᵍ* f))
    reduce (AC.no-id ¬id) =
      inj₂ (λ e → ¬id (Equivalence.to (lemma-4-1-gauss C eq) e))


------------------------------------------------------------------------
-- A decision procedure along the paper's route

-- Eliminate; reduce the restriction by lemma 4.3 until no path
-- variable is left; test the end syntactically.  (Decidability as such
-- is elementary, and the type does not record the route.)

decidable-gauss : (C : Circuit n) → level C ≤ 2 → Dec (⟦ C ⟧ ≋ idPS)
decidable-gauss {n = n} C lv = by ⟦ C ⟧ᴿ refl
  where
  by : (r : Maybe (Σ ℕ (PathSum n (norm C)))) → ⟦ C ⟧ᴿ ≡ r →
       Dec (⟦ C ⟧ ≋ idPS)
  by nothing          eq = no (not-id-gauss C eq)
  by (just (m′ , ξ))  eq =
    reduce (Cliff.corollary-4-4 ξ (⟦⟧ᴿ-Internal C eq) (⟦⟧ᴿ-Ord≤2 C eq lv))
    where
    reduce : Cliff.Reduces ξ → Dec (⟦ C ⟧ ≋ idPS)
    reduce (Cliff.done {ξ′ = ξ′} steps) =
      map′ (Equivalence.from iff) (Equivalence.to iff) (syntactic? ξ′)
      where
      iff = corollary-4-4-any-gauss C eq {ξ′ = ξ′} steps
    reduce (Cliff.no-id ¬id) =
      no (λ e → ¬id (Equivalence.to (lemma-4-1-gauss C eq) e))
