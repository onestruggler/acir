------------------------------------------------------------------------
-- Presentations of groups
--
-- At every width at least four, the H circuit group's abelianization
-- is C2, measured by Hadamard parity.  Its commutator subgroup is
-- precisely the embedded HH group.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.Abelianization (n : ℕ) where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
import Data.Bool.Properties as BP
open import Data.Product.Base using (Σ ; _,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)
import Presentation.Base as PB
import Presentation.GroupLike as GL
open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.Abelianization as Abel
import Examples.Groups.CCX+H.GeneralN.HadamardDecomposition as Decomposition
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH.Abelianization as HHAbel
import Examples.Groups.CCX+HH.GeneralN.Presentation as HHPresentation
import Examples.Groups.CCX+HH.GeneralN.HadamardEmbedding as Embed
import Examples.Groups.CCX+HH.GeneralN.Perfect as Perfect

width = 4 + n
module D = Decomposition n
private module HP = HHPresentation n
open Abel.At width public

private
  preserves : ∀ {u v : HH.Circuit width} → u HP.≈ v →
    width P.⊢ Embed.embed u ≈ Embed.embed v
  preserves {u} {v} eq = P.complete width {u = Embed.embed u} {v = Embed.embed v}
    (Embed.preserve {u = u} {v = v} (HP.sound eq))

  module Lift = HHAbel.At.Universal width (Abel.Relations width) Embed.e
    (λ ax → source-cong (preserves (PB.axiom ax)))
    (λ u v → axiom (Abel.commute u v))

embedded-trivial : ∀ (u : HH.Circuit width) → Embed.embed u ≈ ε
embedded-trivial u = Lift.factor (Perfect.abelian-trivial n u)

section : Bool → H.Circuit width
section = Parity.tail

section-parity : ∀ b → Parity.parity (section b) ≡ b
section-parity = Parity.tail-parity

normalize : ∀ (w : H.Circuit width) → w ≈ section (Parity.parity w)
normalize w = finish (D.decompose w)
  where
  finish : D.Decomposition w → w ≈ section (Parity.parity w)
  finish record { body = u ; bit = b ; correct = eq } =
    trans (source-cong eq)
      (trans (cong (embedded-trivial u) refl)
        (trans left-unit (refl' (Eq.cong section (Eq.sym bit-correct)))))
    where
    bit-correct : Parity.parity w ≡ b
    bit-correct = Eq.trans (Parity.physical-sound {u = w} {v = Embed.embed u • section b}
      (P.sound width eq)) (Parity.factor-parity u b)

complete : ∀ {u v : H.Circuit width} → Parity.parity u ≡ Parity.parity v → u ≈ v
complete {u} {v} eq = trans (normalize u)
  (trans (refl' (Eq.cong section eq)) (sym (normalize v)))

even-derived : ∀ (w : H.Circuit width) → Parity.parity w ≡ false → Derived w
even-derived w even = complete {u = w} {v = ε} even

derived-even : ∀ {w : H.Circuit width} → Derived w → Parity.parity w ≡ false
derived-even = sound

-- These two implications identify the derived subgroup as an actual
-- circuit image, with an HH witness in the forward direction.
derived-to-HH : ∀ (w : H.Circuit width) → Derived w →
  Σ (HH.Circuit width) λ u → width P.⊢ w ≈ Embed.embed u
derived-to-HH w derived = D.even-body w (derived-even derived)

HH-to-derived : ∀ (w : H.Circuit width) (u : HH.Circuit width) →
  width P.⊢ w ≈ Embed.embed u → Derived w
HH-to-derived w u eq = even-derived w
  (Eq.trans (Parity.physical-sound {u = w} {v = Embed.embed u} (P.sound width eq))
    (Parity.expanded u))

-- The parity theorem is an isomorphism of standard group bundles.
C₂ : Group 0ℓ 0ℓ
C₂ = record
  { Carrier = Bool
  ; _≈_ = _≡_
  ; _∙_ = _xor_
  ; ε = false
  ; _⁻¹ = λ b → b
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = Eq.cong₂ _xor_
          }
        ; assoc = BP.xor-assoc
        }
      ; identity = BP.xor-identityˡ , BP.xor-identityʳ
      }
    ; inverse = BP.xor-same , BP.xor-same
    ; ⁻¹-cong = λ eq → eq
    }
  }

private module G = GL.Group-Lemmas (Abel.Relations width) grouplike

abelian-group : Group 0ℓ 0ℓ
abelian-group = G.•-ε-group

private
  module Mono = MonoidMorphisms (Group.rawMonoid abelian-group) (Group.rawMonoid C₂)
  module Maps = GroupMorphisms (Group.rawGroup abelian-group) (Group.rawGroup C₂)

  monoid-homomorphism : Mono.IsMonoidHomomorphism Parity.parity
  monoid-homomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = sound }
      ; homo = λ u v → Eq.refl
      }
    ; ε-homo = Eq.refl
    }

isomorphism : Maps.IsGroupIsomorphism Parity.parity
isomorphism = record
  { isGroupMonomorphism = record
    { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
        abelian-group C₂ monoid-homomorphism
    ; injective = complete
    }
  ; surjective = λ b → section b , λ eq → Eq.trans (sound eq) (section-parity b)
  }
