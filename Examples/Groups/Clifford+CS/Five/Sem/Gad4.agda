------------------------------------------------------------------------
-- Presentations of groups
--
-- A gadget conjugated by an affine circuit, on four wires
--
-- τ α · G V · τ (α⁻¹) denotes the block of V on the images of 0 and e₀
-- under α: the affine circuits denote the permutation operators of their
-- bit maps (Five.Sem.Aff), the gadget its block on 0 and e₀ (a module
-- parameter: Five.Sem.G4 for the gadgets of Five.Gadgets),
-- and conjugating a two-level operator by a permutation renames it
-- (Five.Sem.TL).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; blkOf ; o₄ ; e₄)

module Examples.Groups.Clifford+CS.Five.Sem.Gad4
  (G : Kind → Circuit 4) (g4 : ∀ V → ⟦ G V ⟧ ~ tl (blkOf V) o₄ e₄) where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Nat.Primality using (prime[2])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Word.Base using (_•_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; _~_)
open import Examples.Groups.Clifford+CS.Five.Affine using (τ)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (perm ; module Bij)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm ; bm-inv ; bm-inv′ ; aff4)

import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹)

private
  variable
    k : ℕ

gad₄ : Kind → B.Circuit 4 → Circuit 4
gad₄ V α = τ α • G V • τ (α ⁻¹)

gad₄-sem : (V : Kind) (α : B.Circuit 4) → ⟦ gad₄ V α ⟧ ~ tl (blkOf V) (bm α o₄) (bm α e₄)
gad₄-sem V α =
  ~-trans {s = ⟦ a • (g • a′) ⟧} {t = ⟦ a ⟧ ∙ (⟦ g ⟧ ∙ ⟦ a′ ⟧)} {u = Tl}
    (~-trans {s = ⟦ a • (g • a′) ⟧} {t = ⟦ a ⟧ ∙ ⟦ g • a′ ⟧} {u = ⟦ a ⟧ ∙ (⟦ g ⟧ ∙ ⟦ a′ ⟧)}
      (hom a (g • a′))
      (∙-cong {s = ⟦ a ⟧} {s' = ⟦ a ⟧} {t = ⟦ g • a′ ⟧} {t' = ⟦ g ⟧ ∙ ⟦ a′ ⟧} (~-refl ⟦ a ⟧) (hom g a′)))
    (~-trans {s = ⟦ a ⟧ ∙ (⟦ g ⟧ ∙ ⟦ a′ ⟧)} {t = Pf ∙ (Bl ∙ Pg)} {u = Tl}
      (∙-cong {s = ⟦ a ⟧} {s' = Pf} {t = ⟦ g ⟧ ∙ ⟦ a′ ⟧} {t' = Bl ∙ Pg}
        (aff4 α) (∙-cong {s = ⟦ g ⟧} {s' = Bl} {t = ⟦ a′ ⟧} {t' = Pg} (g4 V) (aff4 (α ⁻¹))))
      (~-trans {s = Pf ∙ (Bl ∙ Pg)} {t = (Pf ∙ Bl) ∙ Pg} {u = Tl}
        (~-sym {s = (Pf ∙ Bl) ∙ Pg} {t = Pf ∙ (Bl ∙ Pg)} (∙-assoc Pf Bl Pg))
        (Bij.conj-tl f f′ (bm-inv′ α) (bm-inv α) (blkOf V) o₄ e₄)))
  where
  a g a′ : Circuit 4
  a  = τ α
  g  = G V
  a′ = τ (α ⁻¹)
  f f′ : Bits 4 → Bits 4
  f  = bm α
  f′ = bm (α ⁻¹)
  Pf Pg Bl Tl : Scaled 4
  Pf = 0 , perm f
  Pg = 0 , perm f′
  Bl = tl (blkOf V) o₄ e₄
  Tl = tl (blkOf V) (f o₄) (f e₄)
