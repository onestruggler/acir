------------------------------------------------------------------------
-- Presentations of groups
--
-- Equivalence of two Clifford circuits over {H, CNOT, R_k, R_k†}, by
-- reducing their miter (Amy, QPL 2018, sections 3 and 4)
--
-- Section 4 says that the reductions, with the isometry restriction
-- and the non-equivalence test, "give a complete, polynomial-time
-- procedure for determining equivalence of Clifford group circuits",
-- and section 3 says how: check that the miter is the identity.  For
-- two circuits over the paper's own gate set the miter is itself a
-- circuit, C₁ followed by C₂† (PathSum.CRK.Miter's miter), and it is
-- Clifford when both are (level at most 2, PathSum.CRK.Adjoint's
-- level-miter).  So corollary 4.4 as the paper proves it -- the
-- restriction ⟦ C ⟧|f(x,y)=x reified by Gaussian elimination, then
-- reduced by lemma 4.3 (PathSum.Gauss.Corollary) -- applies to the
-- miter unchanged, and every result there transfers:
--
--  * the elimination may refute the miter, and then the circuits are
--    not equivalent (equivalence-refuted-gauss);
--  * whatever chain of reductions from the miter's restriction ends
--    without path variables, the circuits are equivalent exactly when
--    it ends with no normalisation left, the inputs as outputs (mod 2)
--    and phase 0 (mod 2^M) (equivalence-any-gauss, and
--    equivalence-anyᵍ-gauss for the rules at any path variable) -- at
--    any level;
--  * for Clifford circuits: they are equivalent exactly when the
--    elimination does not refute and some chain ends at a syntactic
--    identity (equivalence-gauss), equivalently when some chain ends
--    without path variables and every such chain ends at a syntactic
--    identity (equivalence-every-gauss); the reduction by lemma 4.3
--    either refutes or ends at a path-sum that decides the question
--    (equivalence-⟦⟧-gauss), also along any elimination strategy
--    (equivalence-by-gauss); and equivalence is decided along this
--    route (equivalence-decidable-gauss).
--
-- Equivalence is definition 2.3's: equality of the two operators,
-- global phase included.  "Clifford" is read as level C ≤ 2, as in
-- PathSum.Gauss.Corollary: the only phase gates such a circuit can
-- contain are R_0 = I, R_1 = Z and R_2 = S, and their inverses.
--
-- Not formalised: the polynomial time.  Decidability as such is
-- elementary, since a matrix has finitely many entries;
-- equivalence-decidable-gauss goes by the reduction, but its type does
-- not say so.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.Equivalence (M₀ : ℕ) where

open import Data.Integer.Base using (+_)
open import Data.List.Base using (_++_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (trans to ⇔-trans)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (Dec; map′)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (_⟶ᵍ*_)
open import PathSum.Base using (PathSum; idPS; phase; out)
open import PathSum.CRK.Adjoint M using (_†; level-miter)
open import PathSum.CRK.Circuit M using (Circuit; norm; level; ⟦_⟧)
open import PathSum.CRK.Miter M₀ using (miter)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Gauss.Corollary M₀ using
  (⟦_⟧ᴿ; not-id-gauss; corollary-4-4-⟦⟧-gauss; corollary-4-4-any-gauss;
   corollary-4-4-anyᵍ-gauss; corollary-4-4-gauss;
   corollary-4-4-every-gauss; corollary-4-4-by-gauss; decidable-gauss)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (_≈[_]_; μ; x[_]; 0ᴾ)
open import PathSum.Reduction M using (_⟶*_)

import PathSum.Anywhere.Clifford

private
  module AC = PathSum.Anywhere.Clifford M₀

  variable
    n k′ m′ : ℕ


------------------------------------------------------------------------
-- The elimination refutes

-- If the miter's restriction cannot be reified -- no path assignment
-- makes the outputs the inputs -- the circuits are told apart.

equivalence-refuted-gauss : (C₁ C₂ : Circuit n) →
                            ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ nothing →
                            ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivalence-refuted-gauss C₁ C₂ eq e =
  not-id-gauss (C₁ ++ C₂ †) eq (Equivalence.to (miter C₁ C₂) e)


------------------------------------------------------------------------
-- The end of a reduction, syntactically

-- Whatever chain from the miter's reified restriction ends without
-- path variables, the circuits are equivalent exactly when that end is
-- syntactically |x⟩ ↦ |x⟩.  No bound on the level is needed.

equivalence-any-gauss : (C₁ C₂ : Circuit n)
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) → {ξ′ : PathSum n k′ 0} → ξ ⟶* ξ′ →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
equivalence-any-gauss C₁ C₂ eq {ξ′} steps =
  ⇔-trans (miter C₁ C₂)
          (corollary-4-4-any-gauss (C₁ ++ C₂ †) eq {ξ′ = ξ′} steps)

-- The same for chains of the rules at any path variable.

equivalence-anyᵍ-gauss : (C₁ C₂ : Circuit n)
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) → {ξ′ : PathSum n k′ 0} → ξ ⟶ᵍ* ξ′ →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
equivalence-anyᵍ-gauss C₁ C₂ eq {ξ′} steps =
  ⇔-trans (miter C₁ C₂)
          (corollary-4-4-anyᵍ-gauss (C₁ ++ C₂ †) eq {ξ′ = ξ′} steps)


------------------------------------------------------------------------
-- Equivalence of Clifford circuits

-- Two Clifford circuits are equivalent exactly when the elimination
-- does not refute their miter and some chain from its restriction ends
-- at a syntactic identity.

equivalence-gauss : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   ∃ λ m′ → ∃ λ (ξ : PathSum n (norm (C₁ ++ C₂ †)) m′) →
     ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ (ξ′ : PathSum n 0 0) → (ξ ⟶* ξ′) ×
       (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
equivalence-gauss C₁ C₂ lv₁ lv₂ =
  ⇔-trans (miter C₁ C₂)
          (corollary-4-4-gauss (C₁ ++ C₂ †) (level-miter C₁ C₂ lv₁ lv₂))

-- Equivalently: the elimination does not refute, some chain from the
-- restriction ends without path variables, and every such chain ends
-- at a syntactic identity.

equivalence-every-gauss : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 →
  level C₂ ≤ 2 →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   ∃ λ m′ → ∃ λ (ξ : PathSum n (norm (C₁ ++ C₂ †)) m′) →
     ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) ×
     (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → ξ ⟶* ξ′) ×
     (∀ {k′} {ξ′ : PathSum n k′ 0} → ξ ⟶* ξ′ →
        k′ ≡ 0 × (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) ×
        phase ξ′ ≈[ pow M ] 0ᴾ))
equivalence-every-gauss C₁ C₂ lv₁ lv₂ =
  ⇔-trans (miter C₁ C₂)
          (corollary-4-4-every-gauss (C₁ ++ C₂ †)
                                     (level-miter C₁ C₂ lv₁ lv₂))

-- The verdict of the reduction: the elimination or the reduction
-- refutes, or the reduction by lemma 4.3 ends without path variables
-- at a path-sum that is the identity exactly when the circuits are
-- equivalent.

equivalence-⟦⟧-gauss : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 →
  level C₂ ≤ 2 →
  (∃ λ m′ → ∃ λ (ξ : PathSum n (norm (C₁ ++ C₂ †)) m′) →
     ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
       (ξ ⟶* ξ′) × (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivalence-⟦⟧-gauss {n} C₁ C₂ lv₁ lv₂ =
  carry (corollary-4-4-⟦⟧-gauss (C₁ ++ C₂ †) (level-miter C₁ C₂ lv₁ lv₂))
  where
  D = C₁ ++ C₂ †

  carry : (∃ λ m′ → ∃ λ (ξ : PathSum n (norm D) m′) →
             ⟦ D ⟧ᴿ ≡ just (m′ , ξ) ×
             ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
               (ξ ⟶* ξ′) × (⟦ D ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
          ⊎ ¬ (⟦ D ⟧ ≋ idPS) →
          (∃ λ m′ → ∃ λ (ξ : PathSum n (norm D) m′) →
             ⟦ D ⟧ᴿ ≡ just (m′ , ξ) ×
             ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
               (ξ ⟶* ξ′) × (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ξ′ ≋ idPS))
          ⊎ ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
  carry (inj₁ (m′ , ξ , eq , k′ , ξ′ , steps , iff)) =
    inj₁ (m′ , ξ , eq , k′ , ξ′ , steps , ⇔-trans (miter C₁ C₂) iff)
  carry (inj₂ ¬id) = inj₂ (λ e → ¬id (Equivalence.to (miter C₁ C₂) e))

-- The same along any elimination strategy of PathSum.Anywhere.Clifford.

equivalence-by-gauss : (choose : AC.Strategy n) (C₁ C₂ : Circuit n) →
  level C₁ ≤ 2 → level C₂ ≤ 2 →
  (∃ λ m′ → ∃ λ (ξ : PathSum n (norm (C₁ ++ C₂ †)) m′) →
     ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → AC.Follows choose ξ ξ′ ×
       (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
        (k′ ≡ 0 ×
         (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)))
  ⊎ ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivalence-by-gauss {n} choose C₁ C₂ lv₁ lv₂ =
  carry (corollary-4-4-by-gauss choose (C₁ ++ C₂ †)
                                (level-miter C₁ C₂ lv₁ lv₂))
  where
  D = C₁ ++ C₂ †

  Syntactic : ∀ {k′} → PathSum n k′ 0 → Set
  Syntactic {k′} ξ′ =
    k′ ≡ 0 × (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ

  carry : (∃ λ m′ → ∃ λ (ξ : PathSum n (norm D) m′) →
             ⟦ D ⟧ᴿ ≡ just (m′ , ξ) ×
             ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → AC.Follows choose ξ ξ′ ×
               (⟦ D ⟧ ≋ idPS ⇔ Syntactic ξ′))
          ⊎ ¬ (⟦ D ⟧ ≋ idPS) →
          (∃ λ m′ → ∃ λ (ξ : PathSum n (norm D) m′) →
             ⟦ D ⟧ᴿ ≡ just (m′ , ξ) ×
             ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → AC.Follows choose ξ ξ′ ×
               (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ Syntactic ξ′))
          ⊎ ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
  carry (inj₁ (m′ , ξ , eq , k′ , ξ′ , f , iff)) =
    inj₁ (m′ , ξ , eq , k′ , ξ′ , f , ⇔-trans (miter C₁ C₂) iff)
  carry (inj₂ ¬id) = inj₂ (λ e → ¬id (Equivalence.to (miter C₁ C₂) e))


------------------------------------------------------------------------
-- A decision procedure along the paper's route

-- Eliminate at the miter; reduce its restriction by lemma 4.3 until no
-- path variable is left; test the end syntactically.  (Decidability as
-- such is elementary, and the type does not record the route.)

equivalence-decidable-gauss : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 →
                              level C₂ ≤ 2 → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivalence-decidable-gauss C₁ C₂ lv₁ lv₂ =
  map′ (Equivalence.from (miter C₁ C₂)) (Equivalence.to (miter C₁ C₂))
       (decidable-gauss (C₁ ++ C₂ †) (level-miter C₁ C₂ lv₁ lv₂))
