------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoded gadgets denote their two-level blocks, at every width
--
-- Five.Facts4's gadget of kind V on 4 + m wires denotes its block on 0
-- and e₀ (Stable.GadgetSem), so its decoding on two distinct basis
-- states p, q denotes the block on p and q (`gad-dec-sem`, Stable.
-- DecSem.d-sem-pq): the decoding's semantics, gadget by gadget, which
-- with HyperCanon.lemma-sem is what Lemma 8.8 at every width rests on.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.DecGad
  (c4 : Complete 4) (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Data.Bool using (Bool)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (_•_)

open import Notations using (₃₊)

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; blkOf)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl)
import Examples.Groups.Clifford+CS.Stable.GadgetSym as GadgetSym
import Examples.Groups.Clifford+CS.Stable.GadgetSem as GadgetSem
import Examples.Groups.Clifford+CS.Stable.DecSem as DecSem
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Affine.Circuits as Circuits

private
  module GS = GadgetSym f4 f5 tr F
  module SM = GadgetSem f4 f5 tr F

module _ (m : ℕ) where
  private
    module A  = Theory (₃₊ m)
    module Al = Alpha (₃₊ m)
    module C  = Circuits m c4
    module D  = DecSem m c4

  -- The gadget of kind V decoded on distinct p, q denotes its block on
  -- p and q.
  gad-dec-sem : ∀ (V : Kind) (p q : Vec Bool (₄₊ m)) → p ≢ q →
                ⟦ C.⟪ Al.α p q ⟫ʷ • GS.gad V m • C.⟪ A.rev (Al.α p q) ⟫ʷ ⟧ ~ tl (blkOf V) p q
  gad-dec-sem V p q ne = D.d-sem-pq (GS.gad V m) (blkOf V) hG p q ne
    where
    hG = Eq.subst (λ s → ⟦ GS.gad V m ⟧ ~ s) (Eq.cong₂ (tl (blkOf V)) (SM.o≡ m) (SM.e≡ m)) (SM.gad-sem V m)
