------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 4.10 by Reidemeister–Schreier
--
-- Clément gets completeness of Figure 8 for the alphabet P from
-- completeness of Figure 7 for the auxiliary generators (his Theorem
-- 4.4) by the Reidemeister–Schreier method for monoids, which
-- `Normalization/Reidemeister-Schreier` already implements.  This
-- module is the instantiation: Γ is the theory of P, Δ the theory of
-- the auxiliary generators, C the four cosets of Definition A.2 with
-- the identity coset distinguished, f the paper's σ (`Auxiliary.P.asG`)
-- and h the coset action (`Auxiliary.RS.act`).
--
-- The engine's two hypotheses *are* the paper's conditions: `Item-a`
-- is one equation per letter of P, and `Item-b` one per rule of Figure
-- 7 per coset — Appendix A.3.2's raw output, which Appendix A.4 then
-- derives from Figure 8.  Naming them here says exactly what is left:
-- given those two, `reidemeister-schreier` is Theorem 4.10's engine,
-- and nothing else about the method remains to be done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410 (m : ℕ) where

open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_)
open import Word.Base using (Word ; _ᵗ ; [_]ʷ)

open import Notations using (₃₊)

open import Normalization.Reidemeister-Schreier using (module Star-Injective-Full)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets using (Coset ; ⟨ε⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (act)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (_G,_===_)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

------------------------------------------------------------------------
-- The instantiation

module RS = Star-Injective-Full (m P,_===_) (N G,_===_) Coset ⟨ε⟩

------------------------------------------------------------------------
-- The two conditions
--
-- (a) says that reading a letter of P through f and back through the
-- action returns the letter, at the identity coset; (b) that the
-- action is well defined on the relations of Figure 7, at every coset.

Item-a : Set
Item-a = ∀ (x : GenP n) → RS._~_ ([ x ]ʷ , ⟨ε⟩) ((act ᵗ) ⟨ε⟩ (asG x))

Item-b : Set
Item-b = ∀ (c : Coset) {u t : Word (G.Gen N)} →
         N G, u === t → RS._~_ ((act ᵗ) c u) ((act ᵗ) c t)

------------------------------------------------------------------------
-- What they give
--
-- `reidemeister-schreier` is the whole content of the method: the
-- translation of a P-word into the auxiliary generators reflects
-- equivalence.  With Theorem 4.4 — completeness of Figure 7, already a
-- hypothesis of `Completeness` — that is Theorem 4.10.

module Complete (item-a : Item-a) (item-b : Item-b) where

  open RS.Reidemeister-Schreier-Full asG act item-a item-b public
    using (reidemeister-schreier ; fʷ-inj ; g ; lemma-a ; lemma-b)
