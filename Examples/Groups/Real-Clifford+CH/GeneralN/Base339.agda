------------------------------------------------------------------------
-- Presentations of groups
--
-- (339) on four wires, and its rotation pairs, decided (Clément, Lemma
-- D.13)
--
-- `d339 a`: the statement C339 on four wires, the box's control on wire
-- 3 of either colour.  `d339r a b c`: the triply controlled ZX of the
-- box's (320), on wire 0 (b true) or on wire 1 (b false) and coloured a
-- on wire 3, against the triply controlled ZX of the H gate's, on wire 1
-- (c true) or wire 0 (c false) between P ⊗ P on the wires 1 3 and white
-- on wire 2 — the pairs of GeneralN.Box339 on the bottom four wires.
-- Each an evaluation of a few seconds.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base339 where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R)
open import Examples.Groups.Real-Clifford+CH.ProdEval using (allOK ; fam-eval)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; Hg₃ ; P₁₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base322 using (N3F)

-- The triply controlled ZX on wire 0 (true) or on wire 1 (false).
L₄ : Bool → Circuit 4
L₄ true  = ΛZX 3 ↓ᵏ 0
L₄ false = Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓

-- The box's rotation, coloured a on wire 3, and the H gate's, under the
-- swap of the wires 0 1, between P ⊗ P on the wires 1 3 and white on
-- wire 2.
G1r : Bool → Bool → Circuit 4
G1r a b = N3F a (L₄ b)

G2r : Bool → Circuit 4
G2r c = X ↑ ↑ • (P₁₃ • (Ex ↓ • L₄ c • Ex ↓) • P₁₃) • X ↑ ↑

-- Both families are one, over the box, the H gate, the rotation and the
-- negations, swaps and P ⊗ P around them, each read once (ProdEval).
private
  F : List (Circuit 4)
  F = Λ□ 3
    ∷ Hg₃ 0
    ∷ negsB (true ∷ true ∷ true ∷ true ∷ [])
    ∷ negsB (true ∷ true ∷ true ∷ false ∷ [])
    ∷ negsB (true ∷ true ∷ false ∷ true ∷ [])
    ∷ (ΛZX 3 ↓ᵏ 0)
    ∷ Ex ↓
    ∷ X ↑ ↑ ↑
    ∷ X ↑ ↑
    ∷ P₁₃
    ∷ []

  comm : Word ℕ → Word ℕ → Word ℕ × Word ℕ
  comm a b = a • b , b • a

  E : List (Word ℕ × Word ℕ)
  E = comm ([ 2 ]ʷ • [ 0 ]ʷ • [ 2 ]ʷ) ([ 4 ]ʷ • [ 1 ]ʷ • [ 4 ]ʷ)
    ∷ comm ([ 3 ]ʷ • [ 0 ]ʷ • [ 3 ]ʷ) ([ 4 ]ʷ • [ 1 ]ʷ • [ 4 ]ʷ)
    ∷ comm [ 5 ]ʷ ([ 8 ]ʷ • ([ 9 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 9 ]ʷ) • [ 8 ]ʷ)
    ∷ comm [ 5 ]ʷ ([ 8 ]ʷ • ([ 9 ]ʷ • ([ 6 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 6 ]ʷ) • [ 9 ]ʷ) • [ 8 ]ʷ)
    ∷ comm ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) ([ 8 ]ʷ • ([ 9 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 9 ]ʷ) • [ 8 ]ʷ)
    ∷ comm ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) ([ 8 ]ʷ • ([ 9 ]ʷ • ([ 6 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 6 ]ʷ) • [ 9 ]ʷ) • [ 8 ]ʷ)
    ∷ comm ([ 7 ]ʷ • [ 5 ]ʷ • [ 7 ]ʷ) ([ 8 ]ʷ • ([ 9 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 9 ]ʷ) • [ 8 ]ʷ)
    ∷ comm ([ 7 ]ʷ • [ 5 ]ʷ • [ 7 ]ʷ) ([ 8 ]ʷ • ([ 9 ]ʷ • ([ 6 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 6 ]ʷ) • [ 9 ]ʷ) • [ 8 ]ʷ)
    ∷ comm ([ 7 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 7 ]ʷ) ([ 8 ]ʷ • ([ 9 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 9 ]ʷ) • [ 8 ]ʷ)
    ∷ comm ([ 7 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 7 ]ʷ) ([ 8 ]ʷ • ([ 9 ]ʷ • ([ 6 ]ʷ • ([ 6 ]ʷ • [ 5 ]ʷ • [ 6 ]ʷ) • [ 6 ]ʷ) • [ 9 ]ʷ) • [ 8 ]ʷ)
    ∷ []

  all339 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all339 = Eq.refl

d339 : ∀ (a : Bool) →
       Evaluated (col (true ∷ true ∷ true ∷ a ∷ []) (Λ□ 3) • col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0))
                 (col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0) • col (true ∷ true ∷ true ∷ a ∷ []) (Λ□ 3))
d339 true = fam-eval F E all339 0
d339 false = fam-eval F E all339 1

d339r : ∀ (a b c : Bool) → Evaluated (G1r a b • G2r c) (G2r c • G1r a b)
d339r true true true = fam-eval F E all339 2
d339r true true false = fam-eval F E all339 3
d339r true false true = fam-eval F E all339 4
d339r true false false = fam-eval F E all339 5
d339r false true true = fam-eval F E all339 6
d339r false true false = fam-eval F E all339 7
d339r false false true = fam-eval F E all339 8
d339r false false false = fam-eval F E all339 9
