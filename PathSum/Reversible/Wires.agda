------------------------------------------------------------------------
-- Presentations of groups
--
-- The wires of a netlist of Toffoli and CNOT gates (Amy, QPL 2018,
-- table 2)
--
-- Table 2 reports, for each benchmark, how many qubits its circuit
-- uses, and the paper's tool counts them as the distinct wires its
-- gates touch (printVerStats, in Feynman's
-- src/Feynman/Verification/SOP.hs).  Here are the wires of a netlist
-- of PathSum.Reversible: a gate's wires are its controls and its
-- target (wiresᴿ), and u ∈ᴿ gs says that u is a wire of some gate of
-- gs -- a membership, proved by pointing at the gate and at the wire
-- in it, so that a proof about a particular netlist is a path, found
-- by unfolding the netlist, and never a computation.  A concatenation
-- has the wires of its parts, and a netlist's reverse the netlist's.
--
-- PathSum.CRK.Qubits counts the wires of circuits over
-- {H, CNOT, R_k, R_k†} -- decidably -- and shows that the expansion of
-- a netlist into Clifford+T has every wire of the netlist;
-- PathSum.Adder.Wires shows that the adders' netlists have every wire
-- of their layouts.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Reversible.Wires where

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; _++_; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat.Base using (ℕ)

import Data.List.Relation.Unary.Any.Properties as Any

open import PathSum.Reversible using (Gate; ccx; cx)

private
  variable
    N : ℕ


------------------------------------------------------------------------
-- The wires of a gate and of a netlist

-- A gate's controls, then its target.

wiresᴿ : Gate N → List (Fin N)
wiresᴿ (ccx c₁ c₂ t _ _ _) = c₁ ∷ c₂ ∷ t ∷ []
wiresᴿ (cx c t _)          = c ∷ t ∷ []

-- u is a wire of some gate of the netlist.

infix 4 _∈ᴿ_

_∈ᴿ_ : Fin N → List (Gate N) → Set
u ∈ᴿ gs = Any (λ g → u ∈ wiresᴿ g) gs


------------------------------------------------------------------------
-- Concatenation and reversal

-- A concatenation has the wires of each part ...

∈ᴿ-++ˡ : (gs hs : List (Gate N)) {u : Fin N} → u ∈ᴿ gs → u ∈ᴿ gs ++ hs
∈ᴿ-++ˡ gs hs p = Any.++⁺ˡ {xs = gs} {ys = hs} p

∈ᴿ-++ʳ : (gs hs : List (Gate N)) {u : Fin N} → u ∈ᴿ hs → u ∈ᴿ gs ++ hs
∈ᴿ-++ʳ gs hs p = Any.++⁺ʳ gs {ys = hs} p

-- ... and a netlist's reverse the netlist's.

∈ᴿ-reverse : (gs : List (Gate N)) {u : Fin N} → u ∈ᴿ gs → u ∈ᴿ reverse gs
∈ᴿ-reverse gs p = Any.reverse⁺ {xs = gs} p
