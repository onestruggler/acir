------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-wire gadgets denote their blocks
--
-- One evaluation each (Five.Sem.Eval): G-pp, G-rot and G-ki act on 0 and
-- e₀ as the blocks of Five.Sem.Blocks and as the identity elsewhere.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.G4 where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Five.Gadgets.Words using (G-pp ; G-rot ; G-ki)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl ; tlOp)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (same-op)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks

G : Kind → Circuit 4
G kpp  = G-pp
G krot = G-rot
G kki  = G-ki

g4-pp : ⟦ G-pp ⟧ ~ tl (blkOf kpp) o₄ e₄
g4-pp = same-op G-pp 0 (tlOp (blkOf kpp) o₄ e₄) Eq.refl

g4-rot : ⟦ G-rot ⟧ ~ tl (blkOf krot) o₄ e₄
g4-rot = same-op G-rot 0 (tlOp (blkOf krot) o₄ e₄) Eq.refl

g4-ki : ⟦ G-ki ⟧ ~ tl (blkOf kki) o₄ e₄
g4-ki = same-op G-ki 1 (tlOp (blkOf kki) o₄ e₄) Eq.refl

g4 : (V : Kind) → ⟦ G V ⟧ ~ tl (blkOf V) o₄ e₄
g4 kpp  = g4-pp
g4 krot = g4-rot
g4 kki  = g4-ki
