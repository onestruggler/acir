------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli-by-symplectic semidirect product, presented.
--
-- SDProduct builds the relation
--
--   XZ n ⋄ Simplified n ⋄ ConjRelʷ conj
--
-- over the generators XZ.Gen n ⊎ Sym.Gen n: the Pauli rules on the
-- left, the simplified symplectic rules on the right, and the
-- conjugation rule h·n = (conj h n)·h in the middle.  The generic
-- machinery of Presentation.Construct.Properties.SemiDirectProduct
-- turns presentations of the two factors into a presentation of their
-- semidirect product, so all that is needed here is to feed it the
-- pieces.
--
-- Every input is a theorem, so the presentation below is
-- unconditional — no postulate, no hole, no hypothesis:
--
--   * the symplectic factor: Simplified.Presentation.presentation,
--     which presents Sp(2n, ℤ/pℤ);
--   * the Pauli factor: Pauli.Presentation-Alt's presentation, which
--     presents (ℤ/pℤ × ℤ/pℤ)ⁿ;
--   * the two well-definedness hypotheses on the conjugation action:
--     ConjAction.respects-Δ and ConjAction.respects-Γ (the `hyph` and
--     `hypn` that Iso.agda's commented-out attempt left open).
--
-- See the note at the foot of the file on how `Pauli⋊Sp` relates to
-- Semantics.agda's `Pauli⋊Sp-group`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=4 #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Algebra.Bundles using (Group)
open import Level using (0ℓ)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
import Presentation.Construct.Properties.SemiDirectProduct as SDP'

open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (+ₚ-group)
import Examples.Groups.ProjectivePauli.Presentation-Alt p-2 p-prime as XZ
import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as NSim
import Examples.Groups.Symplectic.Simplified.Presentation p-2 p-prime g* g-gen as SimPres
open import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Syntactics p-3 p-prime g* g-gen
  using (module SemiDirect)
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.ConjAction p-3 p-prime g* g-gen as CA

------------------------------------------------------------------------
-- The instantiation, one width at a time

module Semidirect (n : ℕ) where

  -- The two factor relations and the conjugation action, as
  -- SemiDirectProduct expects them.
  Γ = XZ._QRel,_===_ n
  Δ = NSim.Simplified-Relations._QRel,_===_ n
  cj = SemiDirect.conj {n}

  private
    module SDP = SDP' Γ Δ cj

  open PB Γ using () renaming (_≈_ to _≈₁_)

  --------------------------------------------------------------------
  -- The presentation
  --
  -- Every input is a theorem: the two factor presentations, and the two
  -- well-definedness obligations proved in ConjAction.

  private
    module P = SDP.Presentation (CA.respects-Δ {n}) (CA.respects-Γ {n})
                 (+ₚ-group n) (Sp-group n)
                 (XZ.presentation {n}) (SimPres.presentation {n})

  -- The semidirect product of the Pauli group by Sp(2n, ℤ/pℤ), with the
  -- action transported through the two presentations.
  Pauli⋊Sp : Group 0ℓ 0ℓ
  Pauli⋊Sp = P.G1⋊G2

  -- The headline theorem: the relation SDProduct assembles presents
  -- that group.
  presentation : (SemiDirect._QRel,_===_ n) IsPresentationOf Pauli⋊Sp
  presentation = P.dpres

------------------------------------------------------------------------
-- The theorem, at every width

-- The Pauli-by-symplectic relation presents the semidirect product of
-- the Pauli group by Sp(2n, ℤ/pℤ).
presentation : ∀ {n} →
               (SemiDirect._QRel,_===_ n) IsPresentationOf (Semidirect.Pauli⋊Sp n)
presentation {n} = Semidirect.presentation n

------------------------------------------------------------------------
-- A note on the group
--
-- The generic construction builds the semidirect product from the
-- *transported* action — a symplectic element acts on a Pauli by
-- conjugating representative words and re-interpreting — so Pauli⋊Sp is
-- that group rather than definitionally the `Pauli⋊Sp-group` of
-- Semantics.agda, whose action is `ap`.  ConjAction.conjw-sem is
-- exactly the statement that the two actions agree on representatives,
-- so the two groups are isomorphic; identifying them is a transport
-- along that isomorphism.
--
-- For the record, the route the two obligations took (ConjAction) was
--
--   conj-sem : sem ((conj ⁿ') c w) ≡ actg c (sem w)
--
-- for a generator c, extended to words as
--
--   conjw-sem : sem ((conj ʰ') c w) ≡ ap ⟦ c ⟧ (sem w)
--
-- both by induction, from the fourteen generator cases of conj (each a
-- concrete ℤ/pℤ identity, e.g. conj H X = Z against actg H (₁,₀) =
-- (-₀,₁)).  Given the bridge:
--
--   * Respects-Γ: a Pauli rule gives sem u ≡ sem v (soundness), hence
--     actg c (sem u) ≡ actg c (sem v), hence the two conjugates have
--     equal readings, hence they are ≈ by completeness of the Pauli
--     presentation.
--
--   * Respects-Δ: a symplectic rule gives ⟦c⟧ ≈ˢ ⟦d⟧ (soundness of the
--     simplified presentation), i.e. ap ⟦c⟧ ≗ ap ⟦d⟧; the bridge turns
--     that into equal readings, and completeness again concludes.
--
-- So the long rules — M-power, semi-M*CZ, selinger-c10 … c15 — never
-- have to be conjugated by hand: they are handled by soundness of the
-- presentation they already have.
------------------------------------------------------------------------
