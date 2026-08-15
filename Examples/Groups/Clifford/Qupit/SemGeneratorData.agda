------------------------------------------------------------------------
-- Presentations of groups
--
-- Reducing the qupit generator data to a factor set.
--
-- Clifford.Qupit.Semantics.Presented-Extension derives the scalar
-- cocycle of
--
--     1 ─→ A ─→ A ×_γᶜ H ─→ H ─→ 1
--
-- from a record `GeneratorData` — the correction G that one gate carries
-- against a word, plus its congruence, its normalisation, and f-axiom.
-- This file supplies that record from a FACTOR SET for the quotient,
--
--     generator-data : FactorSet ℤ/pℤ (H n) trivial → GeneratorData n,
--
-- which is the qupit copy of Qubit.SemGeneratorData, and shares its two
-- generic halves: the reduction is CocycleGen.Generator-Data.
-- From-FactorSet, and the transport ℤ/pℤ → words is Cyclic.Scalars at
-- order p.  Only the instantiation is new — the two kernels, the trivial
-- action, and the quotient being the Paper-V0 rule set rather than the
-- mod-scalar Figure 8.
--
-- What is NOT here, and is the whole remaining gap: the factor set
-- itself.  For qubits that is Qubit.SemFE, and it is unconditional; the
-- qupit analogue does not exist yet.  Building it needs three things,
-- exactly as SemFE's header lists them:
--
--   * a normalised SECTION of the quotient — one word per class, taking
--     ε to ε — which for qubits comes from a bijective normal form of
--     the mod-scalar rule set with a DISCRETE codomain, so that rep-cong
--     is propositional;
--   * a SCALAR KERNEL theorem: two words equal mod scalars have exact
--     images differing by a power of ω.  Over Clifford.Qupit.Syntactics.
--     _Exact,_===_ this is an induction on Paper-V0 derivations that
--     accumulates `corr`, and it is nearly definitional at a relator,
--     the twisted relator being [ u ]ᵣ === [ corr r ]ₗ • [ v ]ᵣ;
--   * ω-FAITHFULNESS, that ω has order exactly p in the exact group,
--     which makes the defect UNIQUE and hence every cocycle law
--     provable.  This is the semantic one: for qubits it is a theorem
--     about a mod-17 matrix model, and for qupits the natural target is
--     the central extension already in Clifford.Qupit.Semantics, where ω
--     is faithful by construction — but mapping into it needs soundness
--     of the exact rule set, i.e. lifts of S, H and CZ satisfying all
--     sixteen relations with their corrections.  That is the piece of
--     work this file is waiting on.
--
-- A factor set produced that way is the defect of a lifting, which is
-- also what makes the resulting cocycle REALISE corr in the sense of
-- Presented-Extension.Realises — being a cocycle at all is weaker, and
-- the split one is a cocycle too.
--
-- One discipline to keep when that day comes: name the concrete factor
-- set in a module PARAMETER, never in a definition.  Qubit.
-- SemCentralExt's header measures what a definition costs when the value
-- comes from an existence proof — every conversion check forces the
-- whole proof to weak head normal form.  Hence the shape below.
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

module Examples.Groups.Clifford.Qupit.SemGeneratorData
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
import Examples.Groups.Clifford.Qupit.Semantics p-3 p-prime as Sem
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
-- What a factor set would close
--
-- Each of these is the corresponding definition of Presented-Extension
-- with the record filled, so a qupit SemFE would turn all three
-- unconditional at a stroke.

γᶜ : (n : ℕ) → FactorSet Scalars (H n) (Trivial n) → Cocycle (A n) (H n)
γᶜ n γ = PE.γᶜ n (From-FactorSet.generator-data n γ)

Presented-group : (n : ℕ) → FactorSet Scalars (H n) (Trivial n) → Group 0ℓ 0ℓ
Presented-group n γ = PE.Presented-group n (From-FactorSet.generator-data n γ)

Presented-extension : (n : ℕ) (γ : FactorSet Scalars (H n) (Trivial n)) →
                      Extension (AbelianGroup.group (A n)) (H n)
Presented-extension n γ =
  PE.Presented-extension n (From-FactorSet.generator-data n γ)
