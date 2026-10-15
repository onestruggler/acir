------------------------------------------------------------------------
-- Presentations of groups
--
-- The abelianization of the physical H circuit group at every width:
--   zero wires: trivial; one to three wires: C2 x C2;
--   four or more wires: C2, measured by Hadamard parity.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.AbelianizationClassification where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
import Algebra.Construct.Terminal as Terminal
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)
open import Word.Base using (ε)
import Presentation.Base as PB
import Presentation.GroupLike as GL
open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Abelianization as Abel
import Examples.Groups.CCX+H.LowWidthAbelianization as Low
import Examples.Groups.CCX+H.GeneralN.Abelianization as General
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity

model : ℕ → Group 0ℓ 0ℓ
model 0 = Terminal.group
model 1 = Low.One.C₂×C₂
model 2 = Low.Two.C₂×C₂
model 3 = Low.Three.C₂×C₂
model (suc (suc (suc (suc n)))) = General.C₂ n

character : ∀ n → H.Circuit n → Group.Carrier (model n)
character 0 w = tt
character 1 = Low.One.character
character 2 = Low.Two.character
character 3 = Low.Three.character
character (suc (suc (suc (suc n)))) = Parity.parity

abelian-group : ℕ → Group 0ℓ 0ℓ
abelian-group n = GL.Group-Lemmas.•-ε-group (Abel.Relations n) (Abel.At.grouplike n)

private
  module ZeroMono = MonoidMorphisms (Group.rawMonoid (abelian-group 0))
    (Group.rawMonoid (model 0))

  zero-homomorphism : ZeroMono.IsMonoidHomomorphism (character 0)
  zero-homomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ _ → tt }
      ; homo = λ _ _ → tt
      }
    ; ε-homo = tt
    }

isomorphism : ∀ n → GroupMorphisms.IsGroupIsomorphism
  (Group.rawGroup (abelian-group n)) (Group.rawGroup (model n)) (character n)
isomorphism 0 = record
  { isGroupMonomorphism = record
    { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
        (abelian-group 0) (model 0) zero-homomorphism
    ; injective = λ {u} {v} _ → PB.trans (Low.Zero.trivial u) (PB.sym (Low.Zero.trivial v))
    }
  ; surjective = λ _ → ε , λ _ → tt
  }
isomorphism 1 = Low.One.isomorphism
isomorphism 2 = Low.Two.isomorphism
isomorphism 3 = Low.Three.isomorphism
isomorphism (suc (suc (suc (suc n)))) = General.isomorphism n
