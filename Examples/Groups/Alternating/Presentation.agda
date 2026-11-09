------------------------------------------------------------------------
-- Presentations of groups
--
-- The circuit presentations of 𝔄ₙ, among them Lafont's Theorem 4.
--
-- Any sound theory in which the rules of Fig. 10 hold presents the
-- group of even permutations at every width.  ⟦_⟧ is a monoid
-- homomorphism by definition, compatible with the congruence by
-- soundness and injective by completeness (Lemmas 6 and 8), so the
-- circuits embed in 𝔄ₙ (subpresentation-of); by Lemma 6's existence
-- half every even permutation is a denotation (Surjectivity), which
-- promotes the embedding to a presentation (presentation-of).  The
-- three theories:
--
--   presentation          Theorem 4's three relations (p. 267),
--   presentation-Fig10    the seven rules of Fig. 10, i.e. Lemma 8's
--                         rewriting system read as relations,
--   presentation′         Theorem 4 with its second relation replaced
--                         by (ω ↑ • ω)² = 1, Lafont's presentation of
--                         𝔄ₙ by ω₁, …, ω_{n−2} on p. 268.
--
-- The theorem for the alternating group 𝔄ₙ alone is the one at width
-- n: the words over Gen n are those in ω₁, …, ω_{n−2}, and the
-- structural rules are the commutations ω_i ω_j = ω_j ω_i, j > i + 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Presentation where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)
open import Function.Definitions using (Injective)
open import Presentation.Definitions
  using ( _IsPresentationOf_ ; _IsSubPresentationOf_
        ; _IsSubMonoidPresentationOf_ ; isPresentationOf
        ; subMonoidPresentation⇒subPresentation )
open import Relation.Binary.PropositionalEquality using (refl)

import Examples.Groups.Alternating.Completeness as Completeness

open import Examples.Groups.Alternating.Alternative
  using (_SRel′,_===_ ; _VRel′,_===_ ; fig10′)
open import Examples.Groups.Alternating.Derivations using (fig10)
open import Examples.Groups.Alternating.Interpretation using (⟦_⟧)
open import Examples.Groups.Alternating.Rules
  using (Fig10 ; grouplike ; _RRel,_===_ ; _RVRel,_===_ ; axioms)
open import Examples.Groups.Alternating.Semantics using (Alt-group ; _≈ᴬ_)
open import Examples.Groups.Alternating.Soundness
  using (sound ; sound-S ; sound-R ; sound-A)
open import Examples.Groups.Alternating.Surjectivity using (surjective)
open import Examples.Groups.Alternating.Syntactics
  using ( Circuit ; Theory ; _∣_⊢_≈_ ; _SRel,_===_ ; _VRel,_===_
        ; module Lift-Relation )

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Any sound theory with the rules of Fig. 10 presents 𝔄ₙ

module _ (T : Theory) (rules : Fig10 T)
         (sound-T : ∀ {n} {w v : Circuit n} → T n w v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧)
  where

  private
    module L = Lift-Relation T
    module C = Completeness T rules sound-T

  -- ⟦_⟧ embeds the presented monoid in that of 𝔄ₙ.
  submonoid-presentation-of :
    (L._VRel,_===_ n) IsSubMonoidPresentationOf (Group.monoid (Alt-group n))
  submonoid-presentation-of = record
    { ⟦_⟧  = ⟦_⟧
    ; mono = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = sound T sound-T }
          ; homo              = λ _ _ _ → refl
          }
        ; ε-homo = λ _ → refl
        }
      ; injective = C.completeness
      }
    }

  subpresentation-of : (L._VRel,_===_ n) IsSubPresentationOf (Alt-group n)
  subpresentation-of =
    subMonoidPresentation⇒subPresentation submonoid-presentation-of
                                          (grouplike rules)

  presentation-of : (L._VRel,_===_ n) IsPresentationOf (Alt-group n)
  presentation-of =
    isPresentationOf subpresentation-of (surjective T (sound T sound-T))

------------------------------------------------------------------------
-- Theorem 4

soundness : ∀ {w v : Circuit n} →
            _SRel,_===_ ∣ n ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
soundness = sound _SRel,_===_ sound-S

completeness : Injective (_∣_⊢_≈_ _SRel,_===_ n) _≈ᴬ_ ⟦_⟧
completeness = Completeness.completeness _SRel,_===_ fig10 sound-S

subpresentation : (n VRel,_===_) IsSubPresentationOf (Alt-group n)
subpresentation = subpresentation-of _SRel,_===_ fig10 sound-S

presentation : (n VRel,_===_) IsPresentationOf (Alt-group n)
presentation = presentation-of _SRel,_===_ fig10 sound-S

------------------------------------------------------------------------
-- The rules of Fig. 10

presentation-Fig10 : (n RVRel,_===_) IsPresentationOf (Alt-group n)
presentation-Fig10 = presentation-of _RRel,_===_ axioms sound-R

------------------------------------------------------------------------
-- The second relation replaced

presentation′ : (n VRel′,_===_) IsPresentationOf (Alt-group n)
presentation′ = presentation-of _SRel′,_===_ fig10′ sound-A
