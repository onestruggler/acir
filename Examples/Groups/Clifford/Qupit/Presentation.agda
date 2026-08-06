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
-- Of those pieces the symplectic one is available outright:
-- Simplified.Presentation.presentation presents Sp(2n, ℤ/pℤ).  Three
-- are not, and are taken as parameters of `Build` below rather than
-- assumed:
--
--   * respects-Δ / respects-Γ — the conjugation action is well defined,
--     i.e. it respects the symplectic rules in its acting argument and
--     the Pauli rules in its acted-on argument.  These are the two
--     hypotheses SemiDirectProduct2 asks for; they are exactly the
--     `hyph` / `hypn` that Iso.agda's commented-out attempt left open.
--   * p₁ — the Pauli side: XZ n presents (ℤ/pℤ × ℤ/pℤ)ⁿ.  XZ.agda
--     carries the relation and its grouplike witness, but no
--     presentation theorem; Examples.Groups.Pauli.Presentation proves
--     the analogous statement over a different alphabet.
--
-- Once those three land, `presentation` below is the presentation
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
import Examples.Groups.Symplectic.XZ p-2 p-prime as XZ
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
    (G₁ : Group 0ℓ 0ℓ)
    (p₁ : Γ IsPresentationOf G₁)
    where

    private
      module P = SDP.Presentation respects-Δ respects-Γ
                   G₁ (Sp-group n) p₁ (SimPres.presentation {n})

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
-- To turn `Build` into an unconditional theorem, three things are
-- needed; none is assumed anywhere in this file.
--
--   (1) Respects-Γ.  For each symplectic generator c and each Pauli
--       rule, conjugating by c respects it: e.g. for c = H and
--       order-X, conj H (X ^ p) = Z ^ p ≈ ε.  A case analysis over the
--       six XZ rules and the generator shapes, needing the power law
--       for the extended action.
--
--   (2) Respects-Δ.  For each simplified symplectic rule c === d and
--       each Pauli generator, conjugating by c and by d agree.  This is
--       the substantial one — it is the statement that the symplectic
--       rules act consistently on the Paulis, over ~17 rules whose
--       words are long (M-power, semi-M*CZ, selinger-c10 … c15).
--
--   (3) p₁, the Pauli side.  XZ n presents (ℤ/pℤ × ℤ/pℤ)ⁿ: every word
--       normalises to X^a Z^b per wire, which is a normal form,
--       soundness and surjectivity away from a presentation theorem.
--       Alternatively, transport Examples.Groups.Pauli.Presentation
--       along an alphabet isomorphism XZ.Gen n ≅ (Γ-H ⊎^ n), in the
--       style of Iso3.
--
-- Relating `Pauli⋊Sp` to Semantics.agda's `Pauli⋊Sp-group` additionally
-- needs the two actions to agree — that a symplectic element acts on a
-- Pauli by `ap` exactly as conjugation of representative words does —
-- after which the two semidirect products are isomorphic and the
-- presentation transports.
------------------------------------------------------------------------
