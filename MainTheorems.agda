------------------------------------------------------------------------
-- Presentations of groups
--
-- Index of the main results of the qupit development
--
-- This module collects, in one place, the results this branch is for:
-- that each of three rule sets presents the group it is meant to, and
-- that the symplectic coset tower's normal form is unique.  Every result
-- is re-stated with a full type signature and proved by reference to its
-- home module, so this file also serves as a reading guide: the banner
-- of each section names the file where the proof lives.
--
-- The chain runs bottom-up.  The symplectic normal form is what makes
-- the simplified symplectic rules present Sp(2n, ℤ/pℤ); that, with the
-- Pauli group, is what the semidirect construction assembles into
-- Pauli n ⋊ Sp(2n, ℤ/pℤ); the V1 Clifford rules present that; and the
-- paper's Figure 1 rules present it in turn, by transport along an
-- isomorphism of rule sets.
--
-- This is the qupit branch, so the root states only that chain.  The
-- library's other developments — the symmetric, trivial and cyclic
-- groups, the Pauli group on its own, the wreath product, and the
-- Clifford+T and U₃(ℤ[½,i]) amalgamations — are still in the tree, but
-- nothing here reaches them, so they must be typechecked separately.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module MainTheorems where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
import Relation.Binary.PropositionalEquality as Eq

open import Notations using (₁₊)
open import ForStdlib.Data.Fin.Mod using (ℤ ; ℤ* ; _^′_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat using (module PrimeModulus')
open import Presentation.Definitions using (_IsPresentationOf_)

import Examples.Groups.Symplectic.Semantics as SympSem
import Examples.Groups.Symplectic.Normalization.Section as SympSec
import Examples.Groups.Symplectic.Normalization.Uniqueness as SympUnq
import Examples.Groups.Symplectic.Simplified.Syntactics as SympSimSyn
import Examples.Groups.Symplectic.Simplified.Presentation as SympSimPres
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  as QupitSD
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
  as SimV1Syn
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Presentation
  as SimV1Pres
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  as PapV1Syn
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Presentation
  as PapV1Pres

------------------------------------------------------------------------
-- The symplectic normal form is unique
--
-- Home: Examples.Groups.Symplectic.Normalization.Uniqueness.  The engine
-- is the Reidemeister–Schreier coset tower of Symplectic.Normalization,
-- whose well-definedness is proved by induction on the width: each
-- level's obligation needs only faithfulness one level down.
--
-- Uniqueness is the completeness crux — normal forms with equal
-- denotations are equal — and it is what promotes soundness of the
-- interpretation into a presentation theorem.  It is proved outright, so
-- like everything else here it rests on no postulate.

module Symplectic-Theorems (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

  private
    module Sem = SympSem p-2 p-prime
    module Sec = SympSec p-2 p-prime
    module Unq = SympUnq p-2 p-prime

  open Sem using (_≈ˢ_)
  open Sem.Interpretation using (⟦_⟧)
  open Sec using (NF ; [_])

  unique-nf : ∀ n {u v : NF n} → ⟦ [ u ] ⟧ ≈ˢ ⟦ [ v ] ⟧ → u Eq.≡ v
  unique-nf = Unq.⟦[]⟧-injective

------------------------------------------------------------------------
-- Concrete presentations: the symplectic groups, from the simplified
-- rules
--
-- Home: Examples.Groups.Symplectic.Simplified.Presentation.  The
-- simplified rules replace the M-matrices of the full symplectic rules
-- by powers of a single metaplectic generator Mg, so they are stated
-- relative to a primitive root g of ℤ/pℤ, which is what names it.  They
-- present the same group, by transport along the isomorphism of the two
-- rule sets.

module Symplectic-Simplified-Theorems
  (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x Eq.≡ g ^′ toℕ k)
  where

  private
    module Syn  = SympSimSyn  p-2 p-prime g* g-gen
    module Pres = SympSimPres p-2 p-prime g* g-gen

  open Syn.Simplified-Relations using (_QRel,_===_)
  open SympSem p-2 p-prime using (Sp-group)

  -- The simplified rules present Sp(2n, ℤ/pℤ).
  simplified-presentation :
    ∀ n → (n QRel,_===_) IsPresentationOf (Sp-group n)
  simplified-presentation n = Pres.presentation {n}

------------------------------------------------------------------------
-- Concrete presentations: the projective qupit Clifford group
--
-- Homes: Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.
-- Presentation and .Paper-V1.Presentation.  For an odd prime p, the
-- qupit Clifford circuits read **modulo scalars** present the semidirect
-- product of the n-qupit Pauli group and Sp(2n, ℤ/pℤ), which is the
-- projective Clifford group.  Both rule sets below present it, over the
-- same alphabet (Symplectic's H, S, CZ), and like the simplified
-- symplectic rules above both are stated relative to a primitive root g,
-- which their multiplier rules name.
--
-- Pauli⋊Sp itself is built in SemiDirect.Presentation, which feeds the
-- generic semidirect-product machinery its two factors — the simplified
-- symplectic rules above for one, the Pauli rules for the other.
--
--   * V1 is where the work is: the Pauli calculus, the Ex-conjugation
--     rules, and an isomorphism onto the semidirect relation.
--   * Paper-V1 is the paper's Figure 1, with the multiplier spelled over
--     S as SHS' x⁻¹ x.  It has 15 group-specific rules where the R-spelled
--     Paper-V0 has 16: (S • H) ^ 3 = ε is a theorem here rather than an
--     axiom, since under that spelling M₁ *is* that word.  Its theorem is
--     the composite of an isomorphism of rule sets — the identity on
--     words, both being relations over the same alphabet — with
--     Paper-V0's presentation theorem.

module Qupit-Clifford-Theorems
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (2+ p-2))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x Eq.≡ g ^′ toℕ k)
  where

  private
    module SD      = QupitSD   p-3 p-prime g* g-gen
    module SimSyn  = SimV1Syn  p-3 p-prime g* g-gen
    module SimPres = SimV1Pres p-3 p-prime g* g-gen
    module PapSyn  = PapV1Syn  p-3 p-prime g* g-gen
    module PapPres = PapV1Pres p-3 p-prime g* g-gen

  open SD.Semidirect using (Pauli⋊Sp)

  -- The V1 Clifford rules present Pauli n ⋊ Sp(2n, ℤ/pℤ).
  v1-presentation :
    ∀ n → (SimSyn.Clifford-Relations._QRel,_===_ n)
            IsPresentationOf (Pauli⋊Sp n)
  v1-presentation n = SimPres.presentation {n}

  -- …and so do the paper's Figure 1 rules, read modulo scalars.
  clifford-presentation :
    ∀ n → (PapSyn.Clifford-Relations._QRel,_===_ n)
            IsPresentationOf (Pauli⋊Sp n)
  clifford-presentation = PapPres.presentation
