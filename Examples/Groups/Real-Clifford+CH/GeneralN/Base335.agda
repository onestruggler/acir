------------------------------------------------------------------------
-- Presentations of groups
--
-- (335) on four wires, decided (Clément, Lemma D.13)
--
-- The box Λ□ 3 commutes with each colouring of itself whose bit on the
-- box wire is true, by evaluation (about four seconds each): with
-- completeness on four wires, an equation.  The other colourings follow
-- by X on the box wire (GeneralN/BoxComm).  In a module of its own:
-- Agda frees the memory of an evaluation only when its module is done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base335 where

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
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)

-- The eight colourings are one family over the box and the negations
-- of the colourings (col s w is negsB s • w • negsB s), the box read
-- once (ProdEval).
private
  F : List (Circuit 4)
  F = Λ□ 3
    ∷ negsB (true ∷ true ∷ true ∷ true ∷ [])
    ∷ negsB (true ∷ true ∷ true ∷ false ∷ [])
    ∷ negsB (true ∷ true ∷ false ∷ true ∷ [])
    ∷ negsB (true ∷ true ∷ false ∷ false ∷ [])
    ∷ negsB (true ∷ false ∷ true ∷ true ∷ [])
    ∷ negsB (true ∷ false ∷ true ∷ false ∷ [])
    ∷ negsB (true ∷ false ∷ false ∷ true ∷ [])
    ∷ negsB (true ∷ false ∷ false ∷ false ∷ [])
    ∷ []

  comm : Word ℕ → Word ℕ → Word ℕ × Word ℕ
  comm a b = a • b , b • a

  E : List (Word ℕ × Word ℕ)
  E = comm [ 0 ]ʷ ([ 1 ]ʷ • [ 0 ]ʷ • [ 1 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 2 ]ʷ • [ 0 ]ʷ • [ 2 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 3 ]ʷ • [ 0 ]ʷ • [ 3 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 4 ]ʷ • [ 0 ]ʷ • [ 4 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 5 ]ʷ • [ 0 ]ʷ • [ 5 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 6 ]ʷ • [ 0 ]ʷ • [ 6 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 7 ]ʷ • [ 0 ]ʷ • [ 7 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 8 ]ʷ • [ 0 ]ʷ • [ 8 ]ʷ)
    ∷ []

  all335 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all335 = Eq.refl

d335 : ∀ (r : Bits 3) → Evaluated (Λ□ 3 • col (true ∷ r) (Λ□ 3)) (col (true ∷ r) (Λ□ 3) • Λ□ 3)
d335 (true ∷ true ∷ true ∷ []) = fam-eval F E all335 0
d335 (true ∷ true ∷ false ∷ []) = fam-eval F E all335 1
d335 (true ∷ false ∷ true ∷ []) = fam-eval F E all335 2
d335 (true ∷ false ∷ false ∷ []) = fam-eval F E all335 3
d335 (false ∷ true ∷ true ∷ []) = fam-eval F E all335 4
d335 (false ∷ true ∷ false ∷ []) = fam-eval F E all335 5
d335 (false ∷ false ∷ true ∷ []) = fam-eval F E all335 6
d335 (false ∷ false ∷ false ∷ []) = fam-eval F E all335 7
