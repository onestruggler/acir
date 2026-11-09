------------------------------------------------------------------------
-- Presentations of groups
--
-- Frames over the lower three wires, inside four wires
--
-- P is the group of the circuits on wires 0, 1, 2 of a four-wire
-- circuit, which act on both halves (wire 3 = 0 and wire 3 = 1) alike.
-- Its Coxeter system is Width3's: the edge Toffolis T d of the Gray
-- order 000, 001, 011, 010, 110, 111, 101, 100 of the lower wires,
-- here with an idle wire on top (T₄ d = T d ↓ᵏ 1), whose Coxeter
-- relations are Width3's padded (cox₄).  So the frame lemma applies
-- inside four wires: a four-wire circuit b that the T₄ i above j
-- commute with, conjugated by a Coxeter word, depends only on where
-- the word sends the states below j (frame≈), and P-faithfulness for
-- the words of the T₄ d is perm-complete.  P-faithfulness for any
-- three-wire circuits is padded completeness on three wires (P-eq).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.PFrames where

open import Data.Nat.Base using (ℕ)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (⟦_⟧ ; _≐_)
import Examples.Groups.XCXCCX-4bit.Width3 as W3
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox

-- The edge Toffolis of the lower three wires.
T₄ : ℕ → Circuit 4
T₄ d = W3.T d ↓ᵏ 1

cox₄ : Cox.Circuits.Coxeter 8 T₄ (4 VRel,_===_)
cox₄ = record
  { order = λ i p → pad₃ (order i p) 1
  ; braid = λ i p → pad₃ (braid i p) 1
  ; far   = λ i j p q → pad₃ (far i j p q) 1
  }
  where open Cox.Circuits.Coxeter W3.cox

open Cox 8 public using (SG ; CW ; act ; inv ; frame ; frame-act)
open Cox.Circuits 8 T₄ public using (Pc)
open Cox.Circuits.Complete 8 T₄ cox₄ public
  using (Pc-cong ; perm-complete ; Pc-inv ; Pc-inv′ ; Fr ; Fr-conj ; Comm≥ ; stab ; frame≈)

-- Two three-wire circuits with the same function are equal on the
-- lower wires of four.
P-eq : {w v : Circuit 3} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 4 ⊢ w ↓ᵏ 1 ≈ v ↓ᵏ 1
P-eq e = pad₃ (W3.complete₃ e) 1
