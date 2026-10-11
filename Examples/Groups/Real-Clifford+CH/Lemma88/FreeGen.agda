------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary A.5 decoded, at any width with the fragment decoded
-- (Clément, Appendix E.5)
--
-- Given the decoding of every rule (20)–(34) of the Hadamard-free
-- fragment of Figure 8 (`d-ax`), the decoding respects the fragment's
-- congruence (`d-≈`), and so two Hadamard-free words with the same
-- signed permutation have equivalent decodings (`dA5`, Corollary A.5
-- through Unique.A5).  Free supplies `d-ax` from five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (Word ; _ʷ)
open import Notations using (₃₊)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free using (_PF,_===_)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d)

module Examples.Groups.Real-Clifford+CH.Lemma88.FreeGen
  {m : ℕ} (d-ax : ∀ {u t : Word (GenP (₃₊ m))} → m PF, u === t → (₃₊ m) ⊢ (d ʷ) u ≈ (d ʷ) t)
  where

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique as Unique
import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm as SignedPerm
import Examples.Groups.Real-Clifford+CH.Auxiliary.NF as NF

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)
open SignedPerm m using (sp ; _≐_)
open NF m using (HFreeʷ)
open Unique m using (A5)

-- The decoding respects the fragment's congruence.
d-≈ : ∀ {u t : Word (GenP N)} → PB._≈_ (m PF,_===_) u t → (d ʷ) u ≈ (d ʷ) t
d-≈ PB.refl         = refl
d-≈ (PB.sym e)      = sym (d-≈ e)
d-≈ (PB.trans e e′) = trans (d-≈ e) (d-≈ e′)
d-≈ (PB.cong e e′)  = cong (d-≈ e) (d-≈ e′)
d-≈ PB.assoc        = assoc
d-≈ PB.left-unit    = left-unit
d-≈ PB.right-unit   = right-unit
d-≈ (PB.axiom a)    = d-ax a

-- Corollary A.5, decoded.
dA5 : ∀ {u v : Word (GenP N)} → HFreeʷ u → HFreeʷ v → sp u ≐ sp v → (d ʷ) u ≈ (d ʷ) v
dA5 hu hv e = d-≈ (A5 hu hv e)
