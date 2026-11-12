------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport a finite-field factor set to scalar words and extend its
-- generator data. The agreement lemma identifies the generated cocycle
-- with the transported factor set on every pair of words.
--
-- SemFE supplies the Weyl factor set by pullback along the projective
-- presentation. SemSRel verifies the relator corrections; Structural
-- uses agreement to identify the total group with the structural model.
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

module Examples.Groups.Qupit-Clifford.SemGeneratorData
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Level using (0ℓ)

import Presentation.Base as PB

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Construct.SemiDirectProduct using (Action)
import ForStdlib.Algebra.Construct.CentralExtension as CE
open CE using (Cocycle)
import ForStdlib.Algebra.Construct.FactorSetExtension as FSE
open FSE using (FactorSet)

-- The transport ℤ/pℤ → words over the cyclic generator, at order
-- p = ₂₊ p-2.
import Examples.Groups.Cyclic.Scalars as Sc
module Sp = Sc p-2

-- The record to be filled, with its two presented groups.
import Examples.Groups.Qupit-Clifford.Semantics p-3 p-prime as Sem
module PE = Sem.Presented-Extension g* g-gen

open PE using (A ; H ; φ ; GeneratorData)

-- The scalar side of the factor set: ℤ/pℤ written additively, and the
-- only action there is on it.
Scalars : AbelianGroup 0ℓ 0ℓ
Scalars = Sp.A

Trivial : (n : ℕ) → Action (AbelianGroup.rawMonoid Scalars)
                           (Group.rawMonoid (H n))
Trivial n = FSE.trivialAction Scalars (H n)

------------------------------------------------------------------------
-- From a factor set to the generator data
--
-- The factor set is a PARAMETER; see the header.  Its four laws are
-- passed to From-FactorSet one by one, so that nothing has to be
-- rebuilt as a record on the ℤ/pℤ side.

module From-FactorSet (n : ℕ) (γ : FactorSet Scalars (H n) (Trivial n)) where

  private
    module Γ = FactorSet γ
    open FSE.IsNormalisedCocycle Γ.isNormalisedCocycle
      using (f-cong ; f-εˡ ; f-εʳ ; cocycle)

    -- The generic reduction, at this kernel and this transport.
    module FF =
      PE.CGn.From-FactorSet n (φ n)
        (λ _ _ → PB.refl)                 -- the action is trivial
        Scalars Sp.emb Sp.emb-cong Sp.emb-ε Sp.emb-∙
        Γ.f f-cong f-εˡ f-εʳ cocycle

  open FF public using (G ; agree ; G-cong ; G-ε)

  generator-data : GeneratorData n
  generator-data = record
    { G       = FF.G
    ; G-cong  = FF.G-cong
    ; G-ε     = FF.G-ε
    ; f-axiom = FF.G-axiom
    }

------------------------------------------------------------------------
-- Constructions parameterized by the factor set
--
-- Each definition fills the generator-data record from a factor set.
-- SemFE supplies the concrete factor set used by the exact development.

γᶜ : (n : ℕ) → FactorSet Scalars (H n) (Trivial n) → Cocycle (A n) (H n)
γᶜ n γ = PE.γᶜ n (From-FactorSet.generator-data n γ)

Presented-group : (n : ℕ) → FactorSet Scalars (H n) (Trivial n) → Group 0ℓ 0ℓ
Presented-group n γ = PE.Presented-group n (From-FactorSet.generator-data n γ)

Presented-extension : (n : ℕ) (γ : FactorSet Scalars (H n) (Trivial n)) →
                      Extension (AbelianGroup.group (A n)) (H n)
Presented-extension n γ =
  PE.Presented-extension n (From-FactorSet.generator-data n γ)
