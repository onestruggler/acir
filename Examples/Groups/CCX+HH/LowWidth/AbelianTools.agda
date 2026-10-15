------------------------------------------------------------------------
-- Presentations of groups
--
-- Charge soundness and elementary normal-form tools for the physical
-- HH abelianization.  Charge soundness uses ordinary matrix soundness
-- and the complete source presentation, at every circuit width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.LowWidth.AbelianTools where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Nat.Base using (ℕ ; _^_)
open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
import Data.Bool.Properties as BP
open import Data.Product.Base using (_×_ ; _,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Presentation.GroupLike as GL
open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.Abelianization as Abel
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Subgroup.AbelianizationCore as Source
import Examples.Groups.CCX+HH.Subgroup.Charge as Charge
open import Examples.Groups.CCX+HH.Subgroup.Action using (Coset ; c00)
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Complete

module At (n : ℕ) where
  open Abel.At n public
  private module S = Source (2 ^ n)

  charge : H.Circuit n → Coset
  charge w = Charge.state c00 (E.encode w)

  private
    raw : ∀ {u v : H.Circuit n} → P._===_ u v → E.encode u S.≈ E.encode v
    raw {u} {v} ax = S.source-cong
      (Complete.completeness {u = E.encode u} {v = E.encode v}
        (Eq.trans (Q.encoding-correct u)
          (Eq.trans (P.soundness (PB.axiom ax)) (Eq.sym (Q.encoding-correct v)))))

    module ToSource = Universal S.Relations E.e raw
      (λ u v → S.axiom (S.commute u v))

  charge-sound : ∀ {u v} → u ≈ v → charge u ≡ charge v
  charge-sound eq = S.soundness (ToSource.factor eq)

  module NormalForm (B : Set) (character : H.Circuit n → B)
    (rep : B → H.Circuit n) (normalize : ∀ w → w ≈ rep (character w))
    (read : Coset → B) (read-rep : ∀ c → read (charge (rep c)) ≡ c) where

    sound : ∀ {u v} → u ≈ v → character u ≡ character v
    sound {u} {v} eq = Eq.trans (Eq.sym (read-rep (character u)))
      (Eq.trans (Eq.cong read (charge-sound
        (trans (sym (normalize u)) (trans eq (normalize v))))) (read-rep (character v)))

    complete : ∀ {u v} → character u ≡ character v → u ≈ v
    complete {u} {v} eq = trans (normalize u)
      (trans (refl' (Eq.cong rep eq)) (sym (normalize v)))

  power : Bool → H.Circuit n → H.Circuit n
  power false w = ε
  power true w = w

  power-product : ∀ u → (u • u) ≈ ε → ∀ a b →
    (power a u • power b u) ≈ power (a xor b) u
  power-product u uu false false = left-unit
  power-product u uu false true = left-unit
  power-product u uu true false = right-unit
  power-product u uu true true = uu

  pair-power : H.Circuit n → H.Circuit n → Bool × Bool → H.Circuit n
  pair-power u v (a , b) = power a u • power b v

  open PP.Pattern-Assoc (Abel.Relations n) using (by-passoc ; □)

  pair-product : ∀ u v → (u • u) ≈ ε → (v • v) ≈ ε → ∀ a b c d →
    (pair-power u v (a , b) • pair-power u v (c , d)) ≈
      pair-power u v ((a xor c) , (b xor d))
  pair-product u v uu vv a b c d = trans
    (by-passoc ((□ • □) • (□ • □)) ((□ • (□ • □)) • □) Eq.refl)
    (trans (cong (cong refl (axiom (Abel.commute (power b v) (power c u)))) refl)
      (trans (by-passoc ((□ • (□ • □)) • □) ((□ • □) • (□ • □)) Eq.refl)
        (cong (power-product u uu a c) (power-product v vv b d))))

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
        { isMagma = record { isEquivalence = Eq.isEquivalence ; ∙-cong = Eq.cong₂ _xor_ }
        ; assoc = BP.xor-assoc
        }
      ; identity = BP.xor-identityˡ , BP.xor-identityʳ
      }
    ; inverse = BP.xor-same , BP.xor-same
    ; ⁻¹-cong = λ eq → eq
    }
  }

_⊕_ : Bool × Bool → Bool × Bool → Bool × Bool
(a , b) ⊕ (c , d) = (a xor c) , (b xor d)

C₂×C₂ : Group 0ℓ 0ℓ
C₂×C₂ = record
  { Carrier = Bool × Bool
  ; _≈_ = _≡_
  ; _∙_ = _⊕_
  ; ε = false , false
  ; _⁻¹ = λ p → p
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record { isEquivalence = Eq.isEquivalence ; ∙-cong = Eq.cong₂ _⊕_ }
        ; assoc = λ { (a , b) (c , d) (e , f) → Eq.cong₂ _,_ (BP.xor-assoc a c e) (BP.xor-assoc b d f) }
        }
      ; identity = (λ { (a , b) → Eq.cong₂ _,_ (BP.xor-identityˡ a) (BP.xor-identityˡ b) }) ,
          (λ { (a , b) → Eq.cong₂ _,_ (BP.xor-identityʳ a) (BP.xor-identityʳ b) })
      }
    ; inverse = (λ { (a , b) → Eq.cong₂ _,_ (BP.xor-same a) (BP.xor-same b) }) ,
        (λ { (a , b) → Eq.cong₂ _,_ (BP.xor-same a) (BP.xor-same b) })
    ; ⁻¹-cong = λ eq → eq
    }
  }

abelian-group : ℕ → Group 0ℓ 0ℓ
abelian-group n = GL.Group-Lemmas.•-ε-group (Abel.Relations n) (Abel.At.grouplike n)

module Bundle (n : ℕ) (model : Group 0ℓ 0ℓ) where
  private module G = Group model
  private module A = Abel.At n
  private module Mono = MonoidMorphisms (Group.rawMonoid (abelian-group n)) (Group.rawMonoid model)
  private module Maps = GroupMorphisms (Group.rawGroup (abelian-group n)) (Group.rawGroup model)

  build : (character : H.Circuit n → G.Carrier) →
    (∀ {u v} → u A.≈ v → character u G.≈ character v) →
    (∀ {u v} → character u G.≈ character v → u A.≈ v) →
    (∀ u v → character (u • v) G.≈ (character u G.∙ character v)) →
    character ε G.≈ G.ε →
    (rep : G.Carrier → H.Circuit n) → (∀ c → character (rep c) G.≈ c) →
    Maps.IsGroupIsomorphism character
  build character sound complete product unit rep representatives = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
          (abelian-group n) model monoid-homomorphism
      ; injective = complete
      }
    ; surjective = λ c → rep c , λ eq → G.trans (sound eq) (representatives c)
    }
    where
    monoid-homomorphism : Mono.IsMonoidHomomorphism character
    monoid-homomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = sound }
        ; homo = product
        }
      ; ε-homo = unit
      }
