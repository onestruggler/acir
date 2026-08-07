------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figure 8 modulo the global scalar, against the extension
-- presentation of the phaseless Clifford group.
--
-- Two rule sets describe the same group, C(n)/⟨ω⟩:
--
--   1) _CRel,_===_ of Qubit.Selinger.Figure8-Mod-Scalar — Selinger's
--      Figure 8 with the scalar quotiented out (C4 reads SHSHSH = 1),
--      over the gate generators Gen n;
--   2) _Clifford,_===_ (Qubit.Presentation) — the extension presentation
--      of Pauli n by Sp(2n,2), over PauliGen n ⊎ Gen n.
--
-- The comparison is set up as in Examples.Groups.Symplectic.Simplified.
-- Iso, but there the two rule sets share a generating set and the
-- isomorphism is the identity on words.  Here the generating sets differ
-- — (2) names the Paulis as generators, (1) derives them as the words
-- X = HS²H and Z = S² — so the identity will not do, and the builder is
-- Presentation.Morphism.GroupMorphism.StarGroupIsomorphism, which takes a
-- translation in each direction:
--
--     f : PauliGen n ⊎ Gen n → Word (Gen n)     (Paulis to gate words)
--     g : Gen n → Word (PauliGen n ⊎ Gen n)     (gates to themselves)
--
-- What is proved here: f, g, the Figure-8 side's group-likeness, and the
-- round trip f ∘ g.  The two well-definedness obligations and the round
-- trip g ∘ f are taken as module parameters of `Iso` — see the note at
-- the bottom for what each amounts to.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.Iso where

open import Data.Nat using (ℕ ; zero)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product using (_,_ ; ∃)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary.Decidable using (from-yes)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʷ)

import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike)
open import Presentation.Morphism using (module GroupMorphism)

-- Qubit case: fix the prime to 2.
p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥ ; _↑)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z ; _CRel,_===_ ; srel ; lemma-cong↑)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; _Clifford,_===_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The two translations

-- A Pauli generator names a single-qubit X or Z at one position; send it
-- to the corresponding derived word X = HS²H or Z = S² on that wire.
-- The clause structure matches genToVec in Qubit.Presentation.
pauliGen→word : PauliGen n → Word (Gen n)
pauliGen→word {₁₊ zero} (inj₁ tt)        = X
pauliGen→word {₁₊ zero} (inj₂ tt)        = Z
pauliGen→word {₂₊ n}    (inj₁ (inj₁ tt)) = X
pauliGen→word {₂₊ n}    (inj₁ (inj₂ tt)) = Z
pauliGen→word {₂₊ n}    (inj₂ y)         = (pauliGen→word {₁₊ n} y) ↑

-- Paulis become their gate words; gates stay put.
f : PauliGen n ⊎ Gen n → Word (Gen n)
f (inj₁ y)  = pauliGen→word y
f (inj₂ gg) = [ gg ]ʷ

-- Gates embed on the right.
g : Gen n → Word (PauliGen n ⊎ Gen n)
g gg = [ inj₂ gg ]ʷ

------------------------------------------------------------------------
-- The Figure-8 side is group-like
--
-- H² = ε (C2), S⁴ = ε (C3) and CZ² = ε (C5) give each gate a left
-- inverse; a shifted generator inherits its inverse through cong↑.

grouplike-MS : Grouplike (n CRel,_===_)
grouplike-MS (gate₁ H-gate)  = [ gate₁ H-gate ]ʷ , PB.axiom (srel MS.c2)
grouplike-MS (gate₂ CZ-gate) = [ gate₂ CZ-gate ]ʷ , PB.axiom (srel MS.c5)
grouplike-MS (gate₁ S-gate)  = S' • S' • S' , claim
  where
  S' = [ gate₁ S-gate ]ʷ
  -- (S·(S·S))·S has to be rebracketed into S ^ 4 = S·(S·(S·S)).
  claim : PB._≈_ (_ CRel,_===_) ((S' • S' • S') • S') ε
  claim = PB.trans PB.assoc
            (PB.trans (PB.cong PB.refl PB.assoc)
                      (PB.axiom (srel MS.c3)))
grouplike-MS (gg ↥) with grouplike-MS gg
... | inv , eq = inv ↑ , lemma-cong↑ (inv • [ gg ]ʷ) ε eq

------------------------------------------------------------------------
-- The round trip on the Figure-8 side
--
-- f ∘ g is the identity on gate generators, on the nose.

f-left-inv-gen : (x : Gen n) →
                 PB._≈_ (n CRel,_===_) [ x ]ʷ ((f ʷ) (g x))
f-left-inv-gen x = PB.refl

------------------------------------------------------------------------
-- The isomorphism
--
-- Given the three remaining inputs, the two rule sets present the same
-- group, and the isomorphism is (f ʷ).

module Iso
  (n : ℕ)
  (grouplike-Cl : Grouplike (n Clifford,_===_))
  -- Every extension axiom holds among the derived Figure-8 words.
  (f-well-defined : ∀ {w v} → (n Clifford,_===_) w v →
                    PB._≈_ (n CRel,_===_) ((f ʷ) w) ((f ʷ) v))
  -- Every Figure-8 axiom (mod scalar) holds in the extension presentation.
  (g-well-defined : ∀ {u t} → (n CRel,_===_) u t →
                    PB._≈_ (n Clifford,_===_) ((g ʷ) u) ((g ʷ) t))
  -- Each Pauli generator equals its gate word, back in the extension.
  (g-left-inv-gen : (x : PauliGen n ⊎ Gen n) →
                    PB._≈_ (n Clifford,_===_) [ x ]ʷ ((g ʷ) (f x)))
  where

  private
    module GM = GroupMorphism (n Clifford,_===_) (n CRel,_===_)
                  grouplike-Cl grouplike-MS

  open GM.StarGroupIsomorphism f g
         f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen
    public using (isGroupIsomorphism)

------------------------------------------------------------------------
-- What the three parameters amount to
--
-- g-left-inv-gen is the smallest.  On a gate generator it is refl; on a
-- Pauli generator it asks for Z = S² and X = HS²H inside
-- _Clifford,_===_.  Both are available there: the twisted relator for
-- order-S reads [ S² ]ᵣ === [ Z₀ ]ₗ, and the conjugation axiom for H
-- carries Z₀ to X₀, since conj H (inj₂ tt) = pX.
--
-- f-well-defined splits over the extension's three axiom families
-- (Extension.extension-presentation = S ⋄ EmptyRel ⋄ (ConjRelʷ ∪
-- RelTwist)):
--   * left  — the Pauli relations Γ-H ⊕^ n must hold among the derived
--     words: X² = Z² = ε and all commutations.  X and Z on one wire
--     commute only modulo the scalar, which is exactly what `scalar`
--     supplies and why the exact Figure 8 would not do;
--   * mid (left …) — the conjugation axioms, one per gate/Pauli pair,
--     matching conj against C6–C9;
--   * mid (right (tw r̄)) — one per simplified symplectic relator,
--     each holding up to its Pauli correction corr r̄.
--
-- g-well-defined is the converse: derive C1–C15 (with ω = ε) inside the
-- extension presentation.
--
-- These are the two substantive halves and are a large development —
-- essentially Selinger's completeness argument in both directions.
