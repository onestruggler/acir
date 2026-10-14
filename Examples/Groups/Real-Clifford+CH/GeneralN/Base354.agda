------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire facts for (354), decided
--
-- (333) and (334) on four wires: the rotations as words in the H gate
-- (H on wire 0, box wire 1) and the box on wire 2 — the base of the
-- width induction of GeneralN.ZX354, one width below five.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base354 where

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
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg)

-- The box on wire 2 at width 4.
K₄ : Circuit 4
K₄ = Ex ↑ • (Ex ↓ • Λ□ 3 • Ex ↓) • Ex ↑

-- One family over the factors Hg 1, K₄, ΛZX 3, ΛXZ 3, each read once
-- (ProdEval).
private
  F : List (Circuit 4)
  F = Hg 1 ∷ K₄ ∷ ΛZX 3 ∷ ΛXZ 3 ∷ []

  E : List (Word ℕ × Word ℕ)
  E = ([ 0 ]ʷ • [ 1 ]ʷ • [ 0 ]ʷ • [ 1 ]ʷ , [ 2 ]ʷ)
    ∷ ([ 1 ]ʷ • [ 0 ]ʷ • [ 1 ]ʷ • [ 0 ]ʷ , [ 3 ]ʷ)
    ∷ []

  all354 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all354 = Eq.refl

e-333 : Evaluated {4} (Hg 1 • K₄ • Hg 1 • K₄) (ΛZX 3)
e-333 = fam-eval F E all354 0

e-334 : Evaluated {4} (K₄ • Hg 1 • K₄ • Hg 1) (ΛXZ 3)
e-334 = fam-eval F E all354 1
