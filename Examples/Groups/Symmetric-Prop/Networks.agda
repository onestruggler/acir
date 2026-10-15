------------------------------------------------------------------------
-- Presentations of groups
--
-- Swap networks in any PROP: two networks with the same permutation are
-- equal.
--
-- A circuit family with a designated swap (Circuit.Prop) has the swap
-- rules: the swap is an involution and satisfies the Yang–Baxter
-- equation, and the structural rules commute a gate past anything above
-- it.  Those are the relations of Symmetric's circuit presentation of
-- Sₙ, so its circuits map into the family, its transposition to the
-- swap (`net`), respecting the relations (`net-cong`), and the
-- completeness of that presentation carries over: **two swap networks
-- denoting the same permutation are equal** (`perm-≈`), whatever the
-- family's own rules.  Real-Clifford+CH.PermCalc is the same argument
-- for a calculus whose swap is a word rather than a gate.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)
import Circuit.Base

module Examples.Groups.Symmetric-Prop.Networks
  (Gate : ℕ → Set) (Ex-gate : Gate 2)
  (_SRel,_===_ : (n : ℕ) → Circuit.Base.CRel Gate n)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Notations using (₁₊ ; ₂₊)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions using (module _IsPresentationOf_)

open import Circuit.Prop Gate Ex-gate
open Lift-To-Prop _SRel,_===_

import Examples.Groups.Symmetric.Syntactics as S
import Examples.Groups.Symmetric.Presentation as SP
open import Examples.Groups.Symmetric.Semantics using (Permutation′-group)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The map

φ : S.Gen n → Circuit n
φ (S.gate₀ ())
φ (S.gate₁ ())
φ (S.gate₂ S.σ-gate) = σ
φ (g S.↥)           = φ g ↑

-- A network: a circuit of the symmetric presentation, read in the
-- family.
net : Word (S.Gen n) → Circuit n
net = φ ʷ

net-↑ : (w : Word (S.Gen n)) → net (w S.↑) ≡ net w ↑
net-↑ [ g ]ʷ  = Eq.refl
net-↑ ε       = Eq.refl
net-↑ (u • v) = Eq.cong₂ _•_ (net-↑ u) (net-↑ v)

------------------------------------------------------------------------
-- It respects the relations

φ-ax : ∀ {u v : Word (S.Gen n)} → S._VRel,_===_ n u v → n ⊢ net u ≈ net v
φ-ax (S.srel x) with S.top-view x
... | S.padded₂ S.order       = σ-invol
... | S.padded₃ S.yang-baxter = yang-baxter
φ-ax {₁₊ n} (S.cong↑ {w = w} {v = v} r) =
  Eq.subst₂ (λ a b → (₁₊ n) ⊢ a ≈ b) (Eq.sym (net-↑ w)) (Eq.sym (net-↑ v))
            (lemma-cong↑ (net w) (net v) (φ-ax r))
φ-ax (S.comm₁ () g)
φ-ax (S.comm₂ S.σ-gate g) = comm-gate₂-w↑↑ Ex-gate (φ g)
φ-ax (S.ω↑=ω ())

private
  module Cong {n : ℕ} = PP.StarCongruence (S._VRel,_===_ n) (_VRel,_===_ n) φ φ-ax

net-cong : ∀ {u v : Word (S.Gen n)} → PB._≈_ (S._VRel,_===_ n) u v → n ⊢ net u ≈ net v
net-cong = Cong.fʷ-cong

------------------------------------------------------------------------
-- Two networks with the same permutation are equal

module _ {n : ℕ} where
  private
    module SPn = _IsPresentationOf_ (SP.presentation {n})
    open GroupMorphisms (Group.rawGroup SPn.GL.•-ε-group)
                        (Group.rawGroup (Permutation′-group n))

  -- The permutation a network denotes.
  perm : Word (S.Gen n) → Group.Carrier (Permutation′-group n)
  perm = SPn.⟦_⟧

  perm-≈ : ∀ {u v : Word (S.Gen n)} →
           Group._≈_ (Permutation′-group n) (perm u) (perm v) → n ⊢ net u ≈ net v
  perm-≈ {u} {v} e =
    net-cong (IsGroupMonomorphism.injective
                (IsGroupIsomorphism.isGroupMonomorphism SPn.iso) {u} {v} e)
