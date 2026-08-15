------------------------------------------------------------------------
-- Presentations of groups
--
-- Discharging SemCentralExt's generator data.
--
-- Qubit.SemCentralExt derives the scalar cocycle from a record
-- `GeneratorData` — the correction G that one gate carries against a
-- word, plus its congruence, its normalisation, and f-axiom.  This file
-- supplies that record, at every width, from the factor set that
-- Qubit.SemFE already builds in full:
--
--     generator-data : (n : ℕ) → SCE.GeneratorData n
--
-- so the qubit scalar layer's cocycle, group and extension have no
-- hypotheses left.
--
-- Almost nothing here is about qubits.  The reduction — a factor set,
-- transported along any homomorphism, IS the extension of its own
-- generator data — is CocycleGen.Generator-Data.From-FactorSet, and the
-- transport ℤ/8 → words is Cyclic.Scalars at order 8.  What this file
-- adds is the instantiation: the two kernels, the trivial action, and
-- the one application to SemFE's factor set.  Qupit.SemGeneratorData is
-- the same file at ℤ/pℤ and the Paper-V0 quotient.
--
-- The one thing to keep in mind, and the reason the earlier route
-- failed: the concrete factor set is named in a module PARAMETER, never
-- in a definition.  SemCentralExt's header measures what a definition
-- costs — reducing `T ^ toℕ (SemFE.f …)` to weak head normal form forces
-- the section, the bijective normal form and the whole of ScalarKernel,
-- at every conversion check, and conversion reduces before comparing.
-- As a parameter it stays neutral, nothing unfolds, and the single
-- application at the end is only type-checked, its result type
-- mentioning no cocycle.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.SemGeneratorData where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Data.Nat using (ℕ)
open import Level using (0ℓ)

open import Notations
open import Word.Base using (Word ; ε)
import Presentation.Base as PB

open import ForStdlib.Algebra.Construct.Extension using (Extension)
import ForStdlib.Algebra.Construct.CentralExtension as CE
open CE using (Cocycle)
import ForStdlib.Algebra.Construct.FactorSetExtension as FSE
open FSE using (FactorSet)

-- Qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; Circuit)

import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar
  p-2 p-prime as MS

-- The transport ℤ/8 → words over the cyclic generator.
import Examples.Groups.Cyclic.Scalars as Sc
module S8 = Sc 6

-- The two halves being joined: the record to be filled, and the factor
-- set that fills it.
import Examples.Groups.Clifford.Qubit.SemCentralExt as SCE
import Examples.Groups.Clifford.Qubit.SemFE as FE

open SCE using (module CGn ; K ; Q ; φ ; GeneratorData)

------------------------------------------------------------------------
-- From a factor set to the generator data
--
-- The factor set is a PARAMETER; see the header.  Its four laws are
-- passed to From-FactorSet one by one, so that no action on ℤ/8 has to
-- be produced to state them — with the action trivial, the cocycle law
-- of a FactorSet already reads as the plain one.

module From-FactorSet (n : ℕ) (γ : FactorSet FE.K (FE.Q n) (FE.φ n)) where

  private
    module Γ = FactorSet γ
    open FSE.IsNormalisedCocycle Γ.isNormalisedCocycle
      using (f-cong ; f-εˡ ; f-εʳ ; cocycle)

    -- The generic reduction, at this kernel and this transport.
    module FF =
      CGn.From-FactorSet n (φ n)
        (λ _ _ → PB.refl)                 -- the action is trivial
        S8.A S8.emb S8.emb-cong S8.emb-ε S8.emb-∙
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
-- The generator data, at every width
--
-- SemFE.γ is unconditional — its section is discharged there from the
-- bijective normal form of the mod-scalar rule set — so this is too.
-- This application is the only place the concrete factor set is named.

generator-data : (n : ℕ) → GeneratorData n
generator-data n = From-FactorSet.generator-data n (FE.γ n)

------------------------------------------------------------------------
-- What that closes
--
-- SemCentralExt's cocycle, its central extension and its total group,
-- with no hypothesis left.

γᶜ : (n : ℕ) → Cocycle (K n) (Q n)
γᶜ n = SCE.γᶜ n (generator-data n)

Central-group : (n : ℕ) → Group 0ℓ 0ℓ
Central-group n = SCE.Central-group n (generator-data n)

Central-extension : (n : ℕ) → Extension (AbelianGroup.group (K n)) (Q n)
Central-extension n = SCE.Central-extension n (generator-data n)
