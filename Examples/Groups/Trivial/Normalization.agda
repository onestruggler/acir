------------------------------------------------------------------------
-- Presentations of groups
--
-- The normal form for a presentation that collapses every generator.
--
-- Both presentations of the trivial group are trivial for one and the
-- same reason: every generator is already ≈-equal to ε.  That single
-- hypothesis is the parameter gen≈ε, and everything in this module and
-- in Interpretation / UniqueNormalForm is proved once from it, then
-- instantiated twice -- at EmptyRel in Presentation, at TrivialRel in
-- Presentation-Alt.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB

module Examples.Groups.Trivial.Normalization
  {A : Set} (Γ : WRel A)
  (gen≈ε : ∀ x → PB._≈_ Γ [ x ]ʷ ε)
  where

open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Normalization.NormalForm.Propositional as NFBase

open NFBase using (NormalForm ; NormalFormInjective)

open PB Γ using (_≈_)
open _≈_

------------------------------------------------------------------------
-- Every word collapses to ε

-- Generators by hypothesis, ε by reflexivity, and a product by
-- congruence followed by left-unit.
w≈ε : ∀ {w} → w ≈ ε
w≈ε {[ x ]ʷ} = gen≈ε x
w≈ε {ε}      = refl
w≈ε {w • v}  = trans (cong (w≈ε {w}) (w≈ε {v})) left-unit

------------------------------------------------------------------------
-- The normal form

-- Every word is sent to the unique element of ⊤.
nf : Word A → ⊤
nf _ = tt

nf-cong : ∀ {w v} → w ≈ v → nf w ≡ nf v
nf-cong _ = Eq.refl

-- Injectivity carries all the content: any two words are ≈-equal,
-- both being ≈-equal to ε.
nf-injective : ∀ {w v} → nf w ≡ nf v → w ≈ v
nf-injective _ = trans w≈ε (sym w≈ε)

nfp : NormalFormInjective Γ ⊤
nfp = record
  { injection = record
      { to        = nf
      ; cong      = nf-cong
      ; injective = nf-injective
      }
  }

-- The same normal form with a section: the unique normal form is
-- realised by ε.
nfp' : NormalForm Γ ⊤
nfp' = record
  { rightInverse = record
      { to        = nf
      ; from      = λ _ → ε
      ; to-cong   = nf-cong
      ; from-cong = λ { Eq.refl → refl }
      ; inverseʳ  = λ { Eq.refl → sym w≈ε }
      }
  }
