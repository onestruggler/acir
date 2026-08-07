------------------------------------------------------------------------
-- Presentations of groups
--
-- Faithfulness (completeness) of the symplectic representation at
-- width 1: ⟦ w ⟧ ≈ˢ ⟦ v ⟧ implies w ≈ v.
--
-- The proof composes three finished pieces:
--   * the exact width-1 normal form from the 0→1 coset-tower level
--     (Pushing.Tower01 / Pushing.Exact01): every width-1 word is
--     ≈-equal to its normal form's section, gg (nf w) ≈ w;
--   * soundness of the presentation in the symplectic action
--     (SoundnessDirect.sound-ax, lifted here to the congruence);
--   * semantic injectivity of normal forms (NF-Inj.⟦[]⟧-injective) —
--     the normal-form carrier ⊤ × C 1 IS NF 1, and the tower's
--     section gg coincides definitionally with the NF section [_].
--
-- With Faithful 1, SemInj.Injectivity! yields ↑-injectivity at
-- width 1 — the Strategy-B ingredient for the residual halves of the
-- width-2 srel-wd obligations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Faithful1
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB
import Normalization.NormalForm.Setoid as SNF

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Circuit ; Gen ; _QRel,_===_)

open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
  using (_≈ˢ_)
open Sem.Symplectic using (ap)
open Sem.Interpretation using (⟦_⟧)
open import Examples.Groups.Symplectic.SoundnessDirect p-2 p-prime
  using (sound-ax)

import Examples.Groups.Symplectic.Normalization.NF-Inj p-2 p-prime as NFI
import Examples.Groups.Symplectic.Normalization.SemInj p-2 p-prime as SJ
import Examples.Groups.Symplectic.Normalization.Pushing.Tower01
  p-2 p-prime as T01

------------------------------------------------------------------------
-- Soundness, lifted from the axioms to the congruence.

-- Pointwise (≈ˢ applies the action to an argument p), so the monoid
-- laws are definitional and no group structure is needed — the same
-- idiom as Presentation.agda's ⟦⟧-cong.
⟦⟧-sound : ∀ {n} {w v : Circuit n} →
  PB._≈_ (n QRel,_===_) w v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
⟦⟧-sound PB.refl        p = Eq.refl
⟦⟧-sound (PB.sym e)     p = Eq.sym (⟦⟧-sound e p)
⟦⟧-sound (PB.trans e f) p = Eq.trans (⟦⟧-sound e p) (⟦⟧-sound f p)
⟦⟧-sound (PB.cong {w} {_} {_} {v'} e f) p =
  Eq.trans (Eq.cong (ap ⟦ w ⟧) (⟦⟧-sound f p)) (⟦⟧-sound e (ap ⟦ v' ⟧ p))
⟦⟧-sound PB.assoc       p = Eq.refl
⟦⟧-sound PB.left-unit   p = Eq.refl
⟦⟧-sound PB.right-unit  p = Eq.refl
⟦⟧-sound (PB.axiom x)   p = sound-ax x p

------------------------------------------------------------------------
-- The exact width-1 normal form, opened.

open SNF.NormalForm T01.nfp1'
  renaming (nf to nf1 ; inv-nf to gg1 ; inv-nf∘nf=id to gg∘nf=id)
  using ()

------------------------------------------------------------------------
-- Faithfulness at width 1.
--
-- gg1 u and the NF section [ u ] both reduce to ε • [ u .proj₂ ]ᵐˡ,
-- and nf1 w's first component is literally tt, so NF-Inj's
-- ⟦[]⟧-injective applies to nf1 w directly.

faithful1 : SJ.Faithful 1
faithful1 w v hyp =
  P₁.trans (P₁.sym gg∘nf=id)
    (P₁.trans (P₁.refl' (Eq.cong gg1 nfeq)) gg∘nf=id)
  where
  module P₁ = PB (1 QRel,_===_)

  chain : ⟦ gg1 (nf1 w) ⟧ ≈ˢ ⟦ gg1 (nf1 v) ⟧
  chain p = Eq.trans (⟦⟧-sound (gg∘nf=id {w}) p)
            (Eq.trans (hyp p) (Eq.sym (⟦⟧-sound (gg∘nf=id {v}) p)))

  nfeq : nf1 w ≡ nf1 v
  nfeq = NFI.⟦[]⟧-injective (nf1 w) (nf1 v) chain

------------------------------------------------------------------------
-- The payoff: ↑-injectivity at width 1 (the Strategy-B ingredient for
-- the residual halves of the width-2 srel-wd obligations).

module I1 = SJ.Injectivity! 1 faithful1

open I1 public using (↑-inj ; ↑-inj-↑)
