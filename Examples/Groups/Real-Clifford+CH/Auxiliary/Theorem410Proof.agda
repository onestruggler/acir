------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 4.10, from Theorem 4.4
--
-- Both conditions of the Reidemeister–Schreier method are proved:
-- item (a) in `ItemAHH`, item (b) in `ItemB`, with the two long rules
-- (d3*) and (d4*) in `ItemBd3` and `ItemBd4`, all from Figure 10's
-- (65), which `Eq65H` proves at every tuple of four distinct indices.
-- So σ (`P.asG`) reflects equivalence: two words of P whose images over
-- the auxiliary generators are equal in Figure 7 are equal in Figure 8.
-- And σ preserves the semantics on the nose (`asG-sem`), so the paper's
-- Theorem 4.4 — completeness of Figure 7, which it imports — at the
-- width of P gives `Section8.Theorem-4-10`, completeness of Figure 8,
-- the first hypothesis of Section 8's completeness argument.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410Proof (m : ℕ) where

open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_ ; _∙_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP ; −1−1 ; −1X ; XX ; HH ; asG ; ⟦_⟧ᴾ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (⟦_⟧ᴳ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410 m using (Item-b)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.ItemAHH m using (module Complete)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.ItemB m using (module Assemble)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.ItemBd3 m using (d3)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.ItemBd4 m using (d4)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65H m using (eq65-full)

import Examples.Groups.Real-Clifford+CH.BackAndForth as BackAndForth
import Examples.Groups.Real-Clifford+CH.Section8 as Section8
import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

-- Words over the auxiliary generators and over P, read as matrices.
module BG = BackAndForth n (N G.G,_===_) ⟦_⟧ᴳ
module BP = BackAndForth n (m P,_===_) ⟦_⟧ᴾ

-- Theorem 4.4 at the width of P: Figure 7 is complete for the matrices
-- of the auxiliary generators on 2ⁿ indices.
Theorem-4-4 : Set
Theorem-4-4 = ∀ {u t : Word (G.Gen N)} → BG.⟦ u ⟧Y ~ BG.⟦ t ⟧Y → PB._≈_ (N G.G,_===_) u t

-- σ preserves the semantics.
asG-sem : ∀ (u : Word (GenP n)) → BG.⟦ (asG ʷ) u ⟧Y ≡ BP.⟦ u ⟧Y
asG-sem [ −1−1 a b ]ʷ       = Eq.refl
asG-sem [ −1X c a b _ ]ʷ    = Eq.refl
asG-sem [ XX a b c d _ _ ]ʷ = Eq.refl
asG-sem [ HH a b c d _ _ ]ʷ = Eq.refl
asG-sem ε                   = Eq.refl
asG-sem (u • v)             = Eq.cong₂ _∙_ (asG-sem u) (asG-sem v)

-- Item (b), in full.
item-b : Item-b
item-b = Assemble.item-b eq65-full (d3 eq65-full) (d4 eq65-full)

open Complete eq65-full item-b public using (reidemeister-schreier)

-- Theorem 4.10.
theorem-4-10 : Theorem-4-4 → Section8.Theorem-4-10 m
theorem-4-10 t44 {u} {t} eq =
  reidemeister-schreier u t
    (t44 (Eq.subst₂ _~_ (Eq.sym (asG-sem u)) (Eq.sym (asG-sem t)) eq))
