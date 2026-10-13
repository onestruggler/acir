------------------------------------------------------------------------
-- Presentations of groups
--
-- A standard group bundle and isomorphism for the split extension
-- CCX+H = (CCX+HH) ⋊ C₂, at every width at least four.  The action is
-- conjugation by H on wire zero and the inverse has the usual formula.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.SemidirectProduct (n : ℕ) where

open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
import Data.Bool.Properties as BP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)
import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)
open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
import Examples.Groups.CCX+H.Presentation as H
import Examples.Groups.CCX+H.Orthogonal as HO
import Examples.Groups.CCX+H.GeneralN.HadamardAction as Action
import Examples.Groups.CCX+H.GeneralN.HadamardDecomposition as Decomposition
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH.Presentation as HP
import Examples.Groups.CCX+HH.Embedding as Embed

width = 4 + n
private
  module A = Action n
  module D = Decomposition n
  module Source = PB (HP._===_ {width})
  module Target = PB (H.Relations width)
  module SG = Group-Lemmas (HP._===_ {width}) (HP.grouplike width)
  module TG = Group-Lemmas (H.Relations width) (HO.grouplike width)

open A public using (Factor ; realise ; _⋆_ ; α ; twist)

infix 4 _≈_
_≈_ : Factor → Factor → Set
(u , b) ≈ (v , c) = (u HP.≈ v) × (b ≡ c)

unit : Factor
unit = ε , false

inverse : Factor → Factor
inverse (u , b) = twist b (SG._⁻¹ u) , b

private
  twist-cong : ∀ b {u v} → u HP.≈ v → twist b u HP.≈ twist b v
  twist-cong false eq = eq
  twist-cong true eq = A.α-cong eq

  twist-product : ∀ b u v → twist b (u • v) HP.≈ (twist b u • twist b v)
  twist-product false u v = PB.refl
  twist-product true u v = A.α-product u v

  twist-unit : ∀ b → twist b ε HP.≈ ε
  twist-unit false = PB.refl
  twist-unit true = A.α-unit

  product-cong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a ⋆ b) ≈ (a′ ⋆ b′)
  product-cong {u , b} {u′ , .b} {v , c} {v′ , .c} (p , Eq.refl) (q , Eq.refl) =
    PB.cong p (twist-cong b q) , Eq.refl

  associative : ∀ a b c → ((a ⋆ b) ⋆ c) ≈ (a ⋆ (b ⋆ c))
  associative (u , b) (v , c) (w , d) =
    PB.trans PB.assoc
      (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym (A.twist-add b c w))))
        (PB.cong PB.refl (PB.sym (twist-product b v (twist c w))))) ,
    BP.xor-assoc b c d

  identityˡ : ∀ a → (unit ⋆ a) ≈ a
  identityˡ (u , b) = PB.left-unit , Eq.refl

  identityʳ : ∀ a → (a ⋆ unit) ≈ a
  identityʳ (u , b) = PB.trans (PB.cong PB.refl (twist-unit b)) PB.right-unit ,
    BP.xor-identityʳ b

  inverseˡ : ∀ a → (inverse a ⋆ a) ≈ unit
  inverseˡ (u , b) = PB.trans (PB.sym (twist-product b (SG._⁻¹ u) u))
    (PB.trans (twist-cong b (SG.inverseˡ {g = u})) (twist-unit b)) , BP.xor-same b

  inverseʳ : ∀ a → (a ⋆ inverse a) ≈ unit
  inverseʳ (u , false) = SG.inverseʳ {g = u} , Eq.refl
  inverseʳ (u , true) = PB.trans (PB.cong PB.refl (A.α-involutive (SG._⁻¹ u)))
    (SG.inverseʳ {g = u}) , Eq.refl

  inverse-cong : ∀ {a b} → a ≈ b → inverse a ≈ inverse b
  inverse-cong {u , b} {v , .b} (p , Eq.refl) = twist-cong b (SG.⁻¹-cong p) , Eq.refl

semidirect : Group 0ℓ 0ℓ
semidirect = record
  { Carrier = Factor
  ; _≈_ = _≈_
  ; _∙_ = _⋆_
  ; ε = unit
  ; _⁻¹ = inverse
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record
            { refl = PB.refl , Eq.refl
            ; sym = λ { (p , q) → PB.sym p , Eq.sym q }
            ; trans = λ { (p , q) (r , s) → PB.trans p r , Eq.trans q s }
            }
          ; ∙-cong = product-cong
          }
        ; assoc = associative
        }
      ; identity = identityˡ , identityʳ
      }
    ; inverse = inverseˡ , inverseʳ
    ; ⁻¹-cong = inverse-cong
    }
  }

circuit-group : Group 0ℓ 0ℓ
circuit-group = TG.•-ε-group

realise-cong : ∀ {a b} → a ≈ b → Target._≈_ (realise a) (realise b)
realise-cong {u , b} {v , .b} (p , Eq.refl) = PB.cong (Embed.preserves p) PB.refl

realise-injective : ∀ {a b} → Target._≈_ (realise a) (realise b) → a ≈ b
realise-injective {u , b} {v , c} = D.unique u v b c

private
  module Mono = MonoidMorphisms (Monoid.rawMonoid (Group.monoid semidirect))
    (Monoid.rawMonoid (Group.monoid circuit-group))
  module GroupMaps = GroupMorphisms (Group.rawGroup semidirect) (Group.rawGroup circuit-group)

  monoid-homomorphism : Mono.IsMonoidHomomorphism realise
  monoid-homomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = realise-cong }
      ; homo = λ a b → PB.sym (A.realise-product a b)
      }
    ; ε-homo = PB.left-unit
    }

isomorphism : GroupMaps.IsGroupIsomorphism realise
isomorphism = record
  { isGroupMonomorphism = record
    { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
        semidirect circuit-group monoid-homomorphism
    ; injective = realise-injective
    }
  ; surjective = λ w → let d = D.decompose w in
      (D.Decomposition.body d , D.Decomposition.bit d) ,
      λ p → PB.trans (realise-cong p) (PB.sym (D.Decomposition.correct d))
  }
