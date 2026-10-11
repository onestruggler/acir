------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-wire H gates of the proof of (353), and what is decided about
-- them on four wires (Clément, Lemma D.14)
--
-- `Lm` is the H gate of C339 (Col) merged over every colouring of the
-- wires above 3 — the H on wire 3, its box wire on wire 1, black on wire
-- 0, white on wire 2 — and `H○` is Lm under the wire permutation that
-- carries C339's box to the box on wire 1: the H on wire 0, its box wire
-- on wire 3, black on wire 1, white on wire 2.  `H●` is H○ black on wire
-- 2.  These are the paper's two halves of CH on the wires 0 1 viewed as
-- an H gate with its box wire on wire 3 (the proof of (353), case iii):
-- CH is H● H○ (`e-CH`), the two commute (`e-comm`), each is an
-- involution (`e-○²`, `e-●²`), and H● does not see the swap of the
-- wires 1 2 (`e-S`).  Each an evaluation of a few seconds.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base353 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (P₁₃)

-- The transposition of the wires 1 3.
T13 : Circuit 4
T13 = Ex ↑ • Ex ↑ ↑ • Ex ↑

-- C339's box on wire 0 goes to wire 1, its H wire 3 to wire 0, its box
-- wire 1 of the H gate to wire 3.
φ : Circuit 4 → Circuit 4
φ w = Ex ↓ • (T13 • w • T13) • Ex ↓

Lm H○ H● : Circuit 4
Lm = X ↑ ↑ • (P₁₃ • (Ex ↓ • Λ□ 3 • Ex ↓) • P₁₃) • X ↑ ↑
H○ = φ Lm
H● = X ↑ ↑ • H○ • X ↑ ↑

e-CH : Evaluated (CH ↓) (H● • H○)
e-CH = evaluated Eq.refl

e-comm : Evaluated (H○ • H●) (H● • H○)
e-comm = evaluated Eq.refl

e-○² : Evaluated (H○ • H○) ε
e-○² = evaluated Eq.refl

e-●² : Evaluated (H● • H●) ε
e-●² = evaluated Eq.refl

e-S : Evaluated (Ex ↑ • H● • Ex ↑) H●
e-S = evaluated Eq.refl
