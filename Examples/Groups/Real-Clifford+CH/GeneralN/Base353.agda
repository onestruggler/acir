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
open import Data.Bool using (true)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R)
open import Examples.Groups.Real-Clifford+CH.ProdEval using (allOK ; fam-eval)
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

-- The five equations are one family over the factors H○, X ↑ ↑, CH ↓
-- and Ex ↑ (H● being X ↑ ↑ • H○ • X ↑ ↑), decided by one boolean that
-- reads the box in H○ once (ProdEval).
private
  F : List (Circuit 4)
  F = H○ ∷ X ↑ ↑ ∷ CH ↓ ∷ Ex ↑ ∷ []

  h○ h● : Word ℕ
  h○ = [ 0 ]ʷ
  h● = [ 1 ]ʷ • [ 0 ]ʷ • [ 1 ]ʷ

  E : List (Word ℕ × Word ℕ)
  E = ([ 2 ]ʷ , h● • h○)
    ∷ (h○ • h● , h● • h○)
    ∷ (h○ • h○ , ε)
    ∷ (h● • h● , ε)
    ∷ ([ 3 ]ʷ • h● • [ 3 ]ʷ , h●)
    ∷ []

  all353 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all353 = Eq.refl

e-CH : Evaluated (CH ↓) (H● • H○)
e-CH = fam-eval F E all353 0

e-comm : Evaluated (H○ • H●) (H● • H○)
e-comm = fam-eval F E all353 1

e-○² : Evaluated (H○ • H○) ε
e-○² = fam-eval F E all353 2

e-●² : Evaluated (H● • H●) ε
e-●² = fam-eval F E all353 3

e-S : Evaluated (Ex ↑ • H● • Ex ↑) H●
e-S = fam-eval F E all353 4
