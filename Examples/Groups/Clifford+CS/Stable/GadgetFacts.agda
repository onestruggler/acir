------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's gadgets at every width, for Five.Facts4's gadgets
--
-- Stable.GadgetAll needs the four-wire independence (Stable.Gadget4),
-- (F6) on five wires (a module parameter) and the symmetry of the two
-- top controls from six wires on; for Five.Facts4's gadgets that is
-- Stable.GadgetSym.ss-gad₅, from completeness on five wires (`sym`).
-- So their independence of the affine circuit holds at every width
-- (`indep`), and Lemma 8.8 for decoded words over the three kinds
-- reduces to closed four-wire checks (`lemma`, Stable.HyperCanon).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)
import Examples.Groups.Clifford+CS.Stable.Gadget as Gadget

module Examples.Groups.Clifford+CS.Stable.GadgetFacts
  (c4 : Complete 4) (c₅ : Completeᵧ 5)
  (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  (f6 : ∀ V → Gadget.TopTarget 0 c4 (f4 0) (f5 0) (tr 0) (Facts4.G F V))
  where

open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind)
import Examples.Groups.Clifford+CS.Stable.GadgetAll as GadgetAll
import Examples.Groups.Clifford+CS.Stable.GadgetSym as GadgetSym
import Examples.Groups.Clifford+CS.Stable.HyperCanon as HyperCanon
import Examples.Groups.Clifford+CS.Stable.Gadget4 as Gadget4

open Facts4 F using (G)

-- The four-wire input, Stable.Gadget4.
ind₄ : ∀ V → Gadget.Indep₀ 0 c4 (f4 0) (f5 0) (tr 0) (G V)
ind₄ = Gadget4.ind₄ c4 F

private
  module GA = GadgetAll c4 f4 f5 tr
  module GS = GadgetSym f4 f5 tr F

  gad≡ : ∀ V m → GA.gad (G V) (ind₄ V) (f6 V) m ≡ GS.gad V m
  gad≡ V zero    = Eq.refl
  gad≡ V (suc m) = Eq.cong λ⁰ʷ (gad≡ V m)

-- The symmetry of the two top controls, from six wires on.
sym : ∀ V m → Gadget.SwapSym (suc m) c4 (f4 (suc m)) (f5 (suc m)) (tr (suc m))
                (GA.gad (G V) (ind₄ V) (f6 V) (suc m))
sym V m = Eq.subst (λ x → Gadget.SwapSym (suc m) c4 (f4 (suc m)) (f5 (suc m)) (tr (suc m)) (λ⁰ʷ x))
                   (Eq.sym (gad≡ V m)) (GS.ss-gad₅ c₅ V m)

-- The gadget on 4 + m wires, and its independence of the affine circuit.
gad : Kind → ∀ m → Circuit (₄₊ m)
gad V = GA.gad (G V) (ind₄ V) (f6 V)

indep : ∀ V m → Gadget.Indep₀ m c4 (f4 m) (f5 m) (tr m) (gad V m)
indep V = GA.indep (G V) (ind₄ V) (f6 V) (sym V)

-- Lemma 8.8 for decoded words over the three kinds.
open HyperCanon c4 f4 f5 tr Kind G ind₄ f6 sym public using (IW ; inst ; NeW ; lemma ; at-pattern)
