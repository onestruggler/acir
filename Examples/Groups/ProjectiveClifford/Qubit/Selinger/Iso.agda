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
-- isomorphism is the identity on words.  Here the generating sets differ,
-- so the builder is Presentation.Morphism.GroupMorphism.
-- StarGroupIsomorphism, which takes a translation in each direction.
--
-- The supporting material is split off:
--
--   Selinger.Translation — the maps f and g and their word extensions;
--   Selinger.PauliWords  — the calculus of X and Z in Figure 8 mod
--                          scalars (squares, XZ = ZX, disjoint wires);
--   Selinger.PauliVec    — the vector/word dictionary, gate side;
--   Selinger.PauliSide   — the same dictionary, Pauli side;
--   Selinger.Conjugation — fwd-conj, the conjugation axioms;
--   Selinger.Relators    — fwd-tw, the twisted symplectic relators;
--   Selinger.Extension   — the scalar, the shift, and the Pauli
--                          generators as gate words;
--   Selinger.Inverse     — g-well-defined and g-left-inv-gen;
--   Selinger.GroupLike   — group-likeness of both rule sets.
--
-- This module assembles them: the round trip on the Figure-8 side,
-- fwd-pauli, f-well-defined, and the isomorphism itself.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Selinger.Iso where

open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʷ)

import Presentation.Base as PB
open import Presentation.Morphism using (module GroupMorphism)
open import Presentation.Construct.Base
  using (_⋄_⋄_ ; _∪_ ; [_]ₗ ; [_]ᵣ ; ConjRelʷ ; CommRel ; _⊕^_)
open import Presentation.Construct.Properties.Extension using (tw)
import Examples.Groups.Cyclic.Syntactics as CyS

open import ForStdlib.Data.Fin.Mod.Prime.Two
  using (p-2 ; p-prime ; g* ; g-gen)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen)

import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z ; _CRel,_===_ ; lemma-cong↑)

open import Examples.Groups.ProjectiveClifford.Qubit.Presentation
  using (PauliGen ; _Clifford,_===_ ; conj ; corr)
open import Examples.Groups.ProjectivePauli.Presentation p-2 p-prime using (Γ-H)

-- The supporting modules.
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Translation
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.PauliWords
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.GroupLike
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Conjugation using (fwd-conj)
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Relators using (fwd-tw)
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Inverse
  using (g-well-defined ; g-left-inv-gen)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The round trip on the Figure-8 side
--
-- f ∘ g is the identity on gate generators, on the nose.

f-left-inv-gen : (x : Gen n) →
                 PB._≈_ (n CRel,_===_) [ x ]ʷ ((f ʷ) (g x))
f-left-inv-gen x = PB.refl

------------------------------------------------------------------------
-- fwd-pauli
--
-- The Pauli relations hold among the derived words.  At wire 0 they are
-- X² = Z² = ε and XZ = ZX; the `right` branch shifts and recurses; the
-- `mid` branch is disjoint-wire commutation.

pauli-rel : ∀ {n u v} → (Γ-H ⊕^ n) u v →
            PB._≈_ (n CRel,_===_) (Pw u) (Pw v)
pauli-rel {₁₊ zero} (_⋄_⋄_.left  CyS.order) = X²≈ε
pauli-rel {₁₊ zero} (_⋄_⋄_.right CyS.order) = Z²≈ε
pauli-rel {₁₊ zero} (_⋄_⋄_.mid (CommRel.comm _ _)) = XZ.XZ≈ZX zero
pauli-rel {₂₊ m} (_⋄_⋄_.left (_⋄_⋄_.left  CyS.order)) = X²≈ε
pauli-rel {₂₊ m} (_⋄_⋄_.left (_⋄_⋄_.right CyS.order)) = Z²≈ε
pauli-rel {₂₊ m} (_⋄_⋄_.left (_⋄_⋄_.mid (CommRel.comm _ _))) = XZ.XZ≈ZX (₁₊ m)
-- subst rather than rewrite: rewriting here hides the structural
-- recursion from the termination checker.
pauli-rel {₂₊ m} (_⋄_⋄_.right {u} {v} x) =
  Eq.subst₂ (PB._≈_ ((₂₊ m) CRel,_===_))
            (Eq.sym (Pw-↑ m u)) (Eq.sym (Pw-↑ m v))
            (lemma-cong↑ (Pw {₁₊ m} u) (Pw {₁₊ m} v) (pauli-rel x))
pauli-rel {₂₊ m} (_⋄_⋄_.mid (CommRel.comm (inj₁ _) b)) =
  PB.sym (↑Comm.↑-comm-X (₁₊ m) (pauliGen→word b))
pauli-rel {₂₊ m} (_⋄_⋄_.mid (CommRel.comm (inj₂ _) b)) =
  PB.sym (↑Comm.↑-comm-Z (₁₊ m) (pauliGen→word b))

fwd-pauli : ∀ {n u v} → (Γ-H ⊕^ n) u v →
            PB._≈_ (n CRel,_===_) ((f ʷ) [ u ]ₗ) ((f ʷ) [ v ]ₗ)
fwd-pauli {n} {u} {v} x
  rewrite fₗ≡Pw {n} u | fₗ≡Pw {n} v = pauli-rel x

------------------------------------------------------------------------
-- f-well-defined
--
-- Every axiom of the extension presentation holds among the derived
-- Figure-8 words.  The extension relation is (Γ-H ⊕^ n) ⋄ EmptyRel ⋄
-- (ConjRelʷ ∪ RelTwist), so there are exactly three real cases; the
-- EmptyRel factor contributes none.
--
--   fwd-pauli — the Pauli relations, proved above;
--   fwd-conj  — each gate conjugates each Pauli generator as conj says
--               (Selinger.Conjugation);
--   fwd-tw    — each simplified symplectic relator holds up to its
--               Pauli correction corr (Selinger.Relators).

f-well-defined : ∀ {n w v} → (n Clifford,_===_) w v →
                 PB._≈_ (n CRel,_===_) ((f ʷ) w) ((f ʷ) v)
f-well-defined (_⋄_⋄_.left x)  = fwd-pauli x
f-well-defined (_⋄_⋄_.right ())
f-well-defined (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm y x))) = fwd-conj y x
f-well-defined (_⋄_⋄_.mid (_∪_.right (tw r̄)))             = fwd-tw r̄

------------------------------------------------------------------------
-- The isomorphism
--
-- Both translations are well defined and invert each other on
-- generators, so the two rule sets present the same group and the
-- isomorphism is (f ʷ).  Both group-likeness witnesses come from
-- Selinger.GroupLike.

module Iso (n : ℕ) where

  private
    module GM = GroupMorphism (n Clifford,_===_) (n CRel,_===_)
                  (GL.grouplike-Cl n) grouplike-MS

  open GM.StarGroupIsomorphism f g
         f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen
    public using (isGroupIsomorphism)

------------------------------------------------------------------------
-- Where the two halves come from
--
-- f-well-defined: fwd-pauli (here), fwd-conj (Selinger.Conjugation) and
-- fwd-tw (Selinger.Relators).
--
-- g-well-defined and g-left-inv-gen: Selinger.Inverse, on top of
-- Selinger.Extension.  The lemma that unlocked that side is
-- Extension.M≈ε — the scalar M₋₁ = (SH)³ is trivial in the extension
-- presentation.  At p = 2 the multiplicative group ℤ*₂ is trivial, so
-- the simplified relator M-power at exponent 0 already reads ε = M₋₁,
-- with no Pauli correction; nothing about the accumulated correction of
-- lemma-order-SH is needed.
