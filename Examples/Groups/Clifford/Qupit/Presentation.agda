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
-- machinery of Presentation.Construct.Properties.SemiDirectProduct2
-- turns presentations of the two factors into a presentation of their
-- semidirect product, so all that is needed here is to feed it the
-- pieces.
--
-- Both factor presentations are available outright:
-- Simplified.Presentation.presentation presents Sp(2n, ℤ/pℤ), and
-- XZPresentation.presentation presents the Pauli group (ℤ/pℤ × ℤ/pℤ)ⁿ.
--
-- What is still missing is the well-definedness of the action, taken as
-- parameters of `Build` below rather than assumed:
--
--   * respects-Δ / respects-Γ — the conjugation action respects the
--     symplectic rules in its acting argument and the Pauli rules in
--     its acted-on argument.  These are the two hypotheses
--     SemiDirectProduct2 asks for; they are exactly the `hyph` / `hypn`
--     that Iso.agda's commented-out attempt left open.
--
-- Once those two land, `presentation` below is the presentation
-- theorem, with no further work.
--
-- Note on the group: the machinery builds the semidirect product from
-- the *transported* action (a symplectic element acts on a Pauli by
-- conjugating representative words and re-interpreting), so `Pauli⋊Sp`
-- here is that group, not definitionally the `Pauli⋊Sp-group` of
-- Semantics.agda, whose action is `ap` directly.  Identifying the two
-- needs the action-agreement lemma noted at the bottom of this file.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=4 #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module Examples.Groups.Clifford.Qupit.Presentation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Algebra.Bundles using (Group)
open import Level using (0ℓ)
open import Word.Base using (Word ; _ʰ' ; _ⁿ')

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2

open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.Pauli.Semantics p-2 p-prime using (+ₚ-group)
import Examples.Groups.Symplectic.XZ p-2 p-prime as XZ
import Examples.Groups.Symplectic.XZPresentation p-2 p-prime as XZPres
import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as NSim
import Examples.Groups.Symplectic.Simplified.Presentation p-2 p-prime g* g-gen as SimPres
open import Examples.Groups.Clifford.Qupit.SDProduct p-3 p-prime g* g-gen
  using (module SemiDirect)

------------------------------------------------------------------------
-- The instantiation, one width at a time

module Semidirect (n : ℕ) where

  -- The two factor relations and the conjugation action, as
  -- SemiDirectProduct2 expects them.
  Γ = XZ._QRel,_===_ n
  Δ = NSim.Simplified-Relations._QRel,_===_ n
  cj = SemiDirect.conj {n}

  private
    module SDP = SDP2 Γ Δ cj

  open PB Γ using () renaming (_≈_ to _≈₁_)

  --------------------------------------------------------------------
  -- The two well-definedness obligations for the action
  --
  -- Conjugation is given on generators only; for the semidirect
  -- product to be well defined it must respect both factors' rules
  -- once extended to words — in the acting argument (Respects-Δ, the
  -- symplectic rules) and in the acted-on argument (Respects-Γ, the
  -- Pauli rules).

  Respects-Δ : Set
  Respects-Δ = ∀ {c d} (u : Word (XZ.Gen n)) →
               Δ c d → (cj ʰ') c u ≈₁ (cj ʰ') d u

  Respects-Γ : Set
  Respects-Γ = ∀ (c : NSim.Symplectic.Gen n) {u v : Word (XZ.Gen n)} →
               Γ u v → (cj ⁿ') c u ≈₁ (cj ⁿ') c v

  --------------------------------------------------------------------
  -- The presentation
  --
  -- Given the two obligations and a presentation of the Pauli factor,
  -- the symplectic factor's own presentation theorem completes the
  -- input to the generic construction.

  module Build
    (respects-Δ : Respects-Δ)
    (respects-Γ : Respects-Γ)
    where

    private
      module P = SDP.Presentation respects-Δ respects-Γ
                   (+ₚ-group n) (Sp-group n)
                   (XZPres.presentation {n}) (SimPres.presentation {n})

    -- The semidirect product of the Pauli group by Sp(2n, ℤ/pℤ), with
    -- the action transported through the two presentations.
    Pauli⋊Sp : Group 0ℓ 0ℓ
    Pauli⋊Sp = P.G1⋊G2

    -- The headline theorem: the relation SDProduct assembles presents
    -- that group.
    presentation : (SemiDirect._QRel,_===_ n) IsPresentationOf Pauli⋊Sp
    presentation = P.dpres

------------------------------------------------------------------------
-- What remains
--
-- Both obligations reduce to one bridge lemma, rather than to a rule-by
-- rule grind, because the Pauli presentation is now available and so is
-- its completeness.  Write sem for the Pauli reading of an XZ word
-- (XZPresentation) and actg / ⟦_⟧ for the semantic symplectic action
-- (Symplectic.Semantics.Interpretation).  The bridge is
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
--
-- Relating `Pauli⋊Sp` to Semantics.agda's `Pauli⋊Sp-group` additionally
-- needs the two actions to agree — that a symplectic element acts on a
-- Pauli by `ap` exactly as conjugation of representative words does —
-- after which the two semidirect products are isomorphic and the
-- presentation transports.
------------------------------------------------------------------------
