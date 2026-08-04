------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

--{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Uniqueness (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime hiding (⟦_⟧)

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
open import Relation.Nullary.Decidable using (yes ; no)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
open NFBase using (NormalFormInjective ; NormalForm)
import Normalization.CosetNF as CosetNF


--open import Examples.Groups.Symplectic.NewCosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Semantics p-2 p-prime hiding (Symplectic)
open Symplectic

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Data.Sum


private variable
  n : ℕ



open import Data.Nat using (s≤s ; z≤n)

open import Algebra.Bundles using (Group)
open Interpretation

open import Examples.Groups.Symplectic.Normalization.NF-Inj p-2 p-prime
  using (⟦[]⟧-injective)

------------------------------------------------------------------------
-- The normal-form section
--
-- The section is the concrete embedding [_] : NF n → Circuit n from
-- Section.agda; only the normalizer nf-t and its retraction retract-t
-- (soundness of normalization) remain postulated.  Making the section
-- concrete is what lets uniqueness talk about ⟦ [ u ] ⟧ at all.

postulate
  nf-t      : ∀ {n} → Circuit n → NF n
  nf-t-cong : ∀ {n} {w v : Circuit n} → PB._≈_ (n QRel,_===_) w v → nf-t w ≡ nf-t v
  retract-t : ∀ {n} {w : Circuit n} → PB._≈_ (n QRel,_===_) [ nf-t w ] w

nfp'-t : ∀ n → NormalForm (n QRel,_===_) (NF n)
nfp'-t n = record
  { rightInverse = record
      { to        = nf-t
      ; from      = [_]
      ; to-cong   = nf-t-cong
      ; from-cong = λ { Eq.refl → refl }
      ; inverseʳ  = λ { Eq.refl → retract-t }
      }
  }
  where open PB (n QRel,_===_)

------------------------------------------------------------------------
-- Unique normal form for the symplectic semantics
--
-- Because the section is [_], the uniqueness obligation is exactly the
-- semantic injectivity of [_] proved in NF-Inj.

unique-nf : ∀ n →
  NFBase.UniqueNormalForm (n QRel,_===_) (NF n) (Group.setoid (Sp-group n)) ⟦_⟧ (nfp'-t n)
unique-nf n = record
  { unique = λ {u} {v} eq → ⟦[]⟧-injective u v eq
  }
