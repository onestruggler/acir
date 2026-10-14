------------------------------------------------------------------------
-- Presentations of groups
--
-- (336) on four wires, decided (Clément, Lemma D.13)
--
-- The box Λ□ 3 commutes with each colouring of the box on wire 1
-- controlled by wire 0 and the wires 2 3 whose bit on wire 1 is true,
-- by evaluation: with completeness on four wires, an equation.  The
-- other colourings follow by X on wire 1 (GeneralN/BoxComm).  In a
-- module of its own, like Base335.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base336 where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R)
open import Examples.Groups.Real-Clifford+CH.ProdEval using (allOK ; fam-eval)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; B₁)

-- The eight colourings are one family over the box, B₁ 1 and the
-- negations of the colourings, each read once (ProdEval).
private
  F : List (Circuit 4)
  F = Λ□ 3
    ∷ B₁ 1
    ∷ negsB (true ∷ true ∷ true ∷ true ∷ [])
    ∷ negsB (true ∷ true ∷ true ∷ false ∷ [])
    ∷ negsB (true ∷ true ∷ false ∷ true ∷ [])
    ∷ negsB (true ∷ true ∷ false ∷ false ∷ [])
    ∷ negsB (false ∷ true ∷ true ∷ true ∷ [])
    ∷ negsB (false ∷ true ∷ true ∷ false ∷ [])
    ∷ negsB (false ∷ true ∷ false ∷ true ∷ [])
    ∷ negsB (false ∷ true ∷ false ∷ false ∷ [])
    ∷ []

  comm : Word ℕ → Word ℕ → Word ℕ × Word ℕ
  comm a b = a • b , b • a

  E : List (Word ℕ × Word ℕ)
  E = comm [ 0 ]ʷ ([ 2 ]ʷ • [ 1 ]ʷ • [ 2 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 3 ]ʷ • [ 1 ]ʷ • [ 3 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 4 ]ʷ • [ 1 ]ʷ • [ 4 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 5 ]ʷ • [ 1 ]ʷ • [ 5 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 6 ]ʷ • [ 1 ]ʷ • [ 6 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 7 ]ʷ • [ 1 ]ʷ • [ 7 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 8 ]ʷ • [ 1 ]ʷ • [ 8 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 9 ]ʷ • [ 1 ]ʷ • [ 9 ]ʷ)
    ∷ []

  all336 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all336 = Eq.refl

d336 : ∀ (a : Bool) (r : Bits 2) → Evaluated (Λ□ 3 • col (a ∷ true ∷ r) (B₁ 1)) (col (a ∷ true ∷ r) (B₁ 1) • Λ□ 3)
d336 true (true ∷ true ∷ []) = fam-eval F E all336 0
d336 true (true ∷ false ∷ []) = fam-eval F E all336 1
d336 true (false ∷ true ∷ []) = fam-eval F E all336 2
d336 true (false ∷ false ∷ []) = fam-eval F E all336 3
d336 false (true ∷ true ∷ []) = fam-eval F E all336 4
d336 false (true ∷ false ∷ []) = fam-eval F E all336 5
d336 false (false ∷ true ∷ []) = fam-eval F E all336 6
d336 false (false ∷ false ∷ []) = fam-eval F E all336 7
