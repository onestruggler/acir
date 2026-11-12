------------------------------------------------------------------------
-- Presentations of groups
--
-- The original sixteen rules present the structural Weyl group times
-- the sign group. Equality in this model yields a circuit derivation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Structural
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
import Algebra.Construct.DirectProduct as Product
import Algebra.Morphism.Construct.Composition as Compose
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Product using (proj₁ ; proj₂)
open import Function using (_∘_)
open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using (_•_)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
import Presentation.Embedding as Emb

import Examples.Groups.Qupit-Clifford.Semantics p-3 p-prime as Weyl
import Examples.Groups.Qupit-Clifford.Structural
  p-3 p-prime g* g-gen as Bridge
import Examples.Groups.Clifford+MinusOne.Qupit.Semantics
  p-3 p-prime g* g-gen as Sem
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Presentation
  p-3 p-prime g* g-gen as Pres
open import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  p-3 p-prime g* g-gen using (Circuit ; _F,_===_)

StructuralClifford± : ℕ → Group 0ℓ 0ℓ
StructuralClifford± n = Product.group (Weyl.Clifford-group n) Sem.Z₂

module At (n : ℕ) where

  private
    module E = Group (Sem.Clifford± n)
    module S = Group (StructuralClifford± n)
    module B = Bridge.Bridge n
    module I = GroupMorphisms.IsGroupIsomorphism B.structural-iso
    module G = GroupMorphisms E.rawGroup S.rawGroup
    module P = _IsPresentationOf_ (Pres.presentation-Figure1 n)

  to-structural : E.Carrier → S.Carrier
  to-structural (x , s) = B.to-structural x , s

  structural-iso : G.IsGroupIsomorphism to-structural
  structural-iso = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = record
        { isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record
              { cong = λ { {x , s} {y , t} (xy , st) →
                  B.to-cong {x} {y} xy , st } }
            ; homo = λ { (x , s) (y , t) → B.to-∙ x y , Eq.refl }
            }
          ; ε-homo = I.ε-homo , Eq.refl
          }
        ; ⁻¹-homo = λ { (x , s) → I.⁻¹-homo x , Eq.refl }
        }
      ; injective = λ { {x , s} {y , t} (xy , st) →
          B.to-injective {x} {y} xy , st }
      }
    ; surjective = λ { (q , s) →
        let pre = I.surjective q
        in (proj₁ pre , s) , λ { (eq , Eq.refl) → proj₂ pre eq , Eq.refl } }
    }

  interpret : Circuit n → S.Carrier
  interpret = to-structural ∘ P.⟦_⟧

  presentation : (n F,_===_) IsPresentationOf (StructuralClifford± n)
  presentation = record
    { gl = P.gl
    ; ⟦_⟧ = interpret
    ; iso = Compose.isGroupIsomorphism
        (λ {x} {y} {z} → S.trans {x} {y} {z}) P.iso structural-iso
    }

  certify : ∀ {u v} → S._≈_ (interpret u) (interpret v) →
    PB._≈_ (n F,_===_) u v
  certify {u} {v} = Emb.Pres.complete presentation {u} {v}

  sound : ∀ {u v} → PB._≈_ (n F,_===_) u v →
    S._≈_ (interpret u) (interpret v)
  sound {u} {v} = Emb.Pres.sound presentation {u} {v}

  -- A verified replacement inside arbitrary surrounding code. The
  -- equality premise includes both phase and sign, not just the action.
  replace : (l r : Circuit n) {u v : Circuit n} →
    S._≈_ (interpret u) (interpret v) →
    PB._≈_ (n F,_===_) (l • (u • r)) (l • (v • r))
  replace l r {u} {v} eq = PB.cong PB.refl
    (PB.cong (certify {u} {v} eq) PB.refl)
