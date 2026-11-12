------------------------------------------------------------------------
-- Presentations of groups
--
-- From the presented scalar extension to the structural Weyl extension.
-- The map reads the scalar word in Z/pZ and the gate word in Pauli ⋊ Sp.
-- CocycleGen's agreement lemma proves preservation of multiplication;
-- the two factor presentations prove injectivity and surjectivity.
-- No interpretation as complex matrices is used or established here.
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

module Examples.Groups.Qupit-Clifford.Structural
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module GroupMorphisms ; module MonoidMorphisms)
import Algebra.Morphism.Construct.Composition as Compose
open import Data.Product using (proj₁ ; proj₂)
open import Data.Sum using (_⊎_)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using (Word ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as Props
open import Presentation.Definitions using (_IsPresentationOf_)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import ForStdlib.Algebra.Construct.CentralExtension using (Cocycle)

import Examples.Groups.Cyclic.Presentation as CyP
import Examples.Groups.Cyclic.Scalars as CySc
import Examples.Groups.Cyclic.Uniqueness as CyU
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Presentation
  p-3 p-prime g* g-gen as Pap
import Examples.Groups.Qupit-Clifford.Syntactics
  p-3 p-prime g* g-gen as Syn
import Examples.Groups.Qupit-Clifford.Semantics p-3 p-prime as Sem
import Examples.Groups.Qupit-Clifford.SemFE p-3 p-prime g* g-gen as FE
import Examples.Groups.Qupit-Clifford.SemGeneratorData
  p-3 p-prime g* g-gen as SGD
import Examples.Groups.Qupit-Clifford.Presentation
  p-3 p-prime g* g-gen as Exact

module PE = Sem.Presented-Extension g* g-gen
module Sc = CySc p-2
module KP = _IsPresentationOf_ (CyP.presentation {p-1})
module KI = GroupMorphisms.IsGroupIsomorphism KP.iso
module KB = PB Syn.Scalar-relation
module KProps = Props Syn.Scalar-relation

read-scalar : Word Syn.ScalarGen → ℤ ₚ
read-scalar = KP.⟦_⟧

read-emb : ∀ k → read-scalar (Sc.emb k) ≡ k
read-emb k = Eq.trans
  (KI.⟦⟧-cong (KB.sym (KProps.^'=^ {toℕ k} {Syn.ω})))
  (CyU.pow-id k)

module Bridge (n : ℕ) where

  private
    module E = Group (PE.Presented-group n (Exact.exact-generator-data n))
    module S = Group (Sem.Clifford-group n)
    module QP = _IsPresentationOf_ (Pap.presentation n)
    module QI = GroupMorphisms.IsGroupIsomorphism QP.iso
    module W = FE.Weyl n
    module F = SGD.From-FactorSet n W.factorSet
    module C = Cocycle (PE.γᶜ n (Exact.exact-generator-data n))

  to-structural : E.Carrier → S.Carrier
  to-structural (a , u) = Sem.ω^ read-scalar a , W.⟦ u ⟧

  cocycle-agrees : ∀ u v →
    read-scalar (C.c u v) ≡ Sem.cocy n W.⟦ u ⟧ W.⟦ v ⟧
  cocycle-agrees u v =
    Eq.trans (KI.⟦⟧-cong (F.agree u v)) (read-emb (W.fa u v))

  to-cong : ∀ {x y} → E._≈_ x y → S._≈_ (to-structural x) (to-structural y)
  to-cong (a≈b , u≈v) = Eq.cong Sem.ω^_ (KI.⟦⟧-cong a≈b) , W.⟦⟧-cong u≈v

  to-∙ : ∀ x y →
    S._≈_ (to-structural (x E.∙ y)) (to-structural x S.∙ to-structural y)
  to-∙ (a , u) (b , v) = Eq.cong Sem.ω^_ scalar , W.⟦⟧-∙ u v
    where
    scalar : read-scalar ((a • b) • C.c u v) ≡
      (read-scalar a + read-scalar b) + Sem.cocy n W.⟦ u ⟧ W.⟦ v ⟧
    scalar = Eq.trans (KI.∙-homo (a • b) (C.c u v))
      (Eq.cong₂ _+_ (KI.∙-homo a b) (cocycle-agrees u v))

  to-injective : ∀ {x y} →
    S._≈_ (to-structural x) (to-structural y) → E._≈_ x y
  to-injective (a≡b , u≈v) =
    KI.injective (Eq.cong Sem.Scalar.exponent a≡b) , QI.injective u≈v

  private
    module M = MonoidMorphisms E.rawMonoid S.rawMonoid
    module G = GroupMorphisms E.rawGroup S.rawGroup

    hom : M.IsMonoidHomomorphism to-structural
    hom = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record
          { cong = λ {x} {y} → to-cong {x} {y} }
        ; homo = to-∙
        }
      ; ε-homo = Eq.cong Sem.ω^_ KI.ε-homo , W.⟦⟧-ε
      }

  structural-iso : G.IsGroupIsomorphism to-structural
  structural-iso = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism =
          isMonoidHomomorphism⇒isGroupHomomorphism
            (PE.Presented-group n (Exact.exact-generator-data n))
            (Sem.Clifford-group n) hom
      ; injective = λ {x} {y} → to-injective {x} {y}
      }
    ; surjective = λ { (Sem.ω^ e , q) →
        let a = KI.surjective e
            u = QI.surjective q
        in (proj₁ a , proj₁ u) , λ { (ea , eu) →
          Eq.cong Sem.ω^_ (proj₂ a ea) , proj₂ u eu } }
    }

  private
    module XP = _IsPresentationOf_ (Exact.presentation-exact n)

  -- The interpretation is specified, not merely an existential isomorphism.
  interpret : Word (Syn.ScalarGen ⊎ Syn.Gen n) → S.Carrier
  interpret = to-structural ∘ XP.⟦_⟧

  structural-presentation : (n Syn.Exact,_===_) IsPresentationOf (Sem.Clifford-group n)
  structural-presentation = record
    { gl = XP.gl
    ; ⟦_⟧ = interpret
    ; iso = Compose.isGroupIsomorphism
        (λ {x} {y} {z} → S.trans {x} {y} {z}) XP.iso structural-iso
    }

  -- A client supplies equality in the structural model and receives a
  -- derivation in the original exact congruence. No rewrite search is run.
  certify : ∀ {u v} → S._≈_ (interpret u) (interpret v) →
    PB._≈_ (n Syn.Exact,_===_) u v
  certify {u} {v} =
    GroupMorphisms.IsGroupIsomorphism.injective
      (_IsPresentationOf_.iso structural-presentation) {u} {v}
