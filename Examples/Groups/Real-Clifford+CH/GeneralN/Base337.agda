------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotation pairs of (337), decided (Clément, Lemma D.13)
--
-- `d337r b c`: the triply controlled ZX of the box's (320), on wire 0
-- (b true) or on wire 1 (b false), against the triply controlled ZX of
-- the H gate's, on wire 0 (c true) or on wire 1 (c false), between P ⊗ P
-- on the wires 0 1 and white on wire 2 — the rotation pairs of
-- GeneralN.Box337 on the bottom four wires.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base337 where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R)
open import Examples.Groups.Real-Clifford+CH.ProdEval using (allOK ; fam-eval)

-- The triply controlled ZX on wire 0 (true) or on wire 1 (false).
U₄ : Bool → Circuit 4
U₄ true  = ΛZX 3
U₄ false = Ex ↓ • ΛZX 3 • Ex ↓

-- The H gate's, between P ⊗ P on the wires 0 1 and white on wire 2.
G2 : Bool → Circuit 4
G2 c = X ↑ ↑ • (PP ↓ • U₄ c • PP ↓) • X ↑ ↑

-- The four commutations are one family over ΛZX 3, the swap, X and
-- P ⊗ P, each read once (ProdEval).
private
  F : List (Circuit 4)
  F = ΛZX 3
    ∷ Ex ↓
    ∷ X ↑ ↑
    ∷ PP ↓
    ∷ []

  comm : Word ℕ → Word ℕ → Word ℕ × Word ℕ
  comm a b = a • b , b • a

  E : List (Word ℕ × Word ℕ)
  E = comm [ 0 ]ʷ ([ 2 ]ʷ • ([ 3 ]ʷ • [ 0 ]ʷ • [ 3 ]ʷ) • [ 2 ]ʷ)
    ∷ comm [ 0 ]ʷ ([ 2 ]ʷ • ([ 3 ]ʷ • ([ 1 ]ʷ • [ 0 ]ʷ • [ 1 ]ʷ) • [ 3 ]ʷ) • [ 2 ]ʷ)
    ∷ comm ([ 1 ]ʷ • [ 0 ]ʷ • [ 1 ]ʷ) ([ 2 ]ʷ • ([ 3 ]ʷ • [ 0 ]ʷ • [ 3 ]ʷ) • [ 2 ]ʷ)
    ∷ comm ([ 1 ]ʷ • [ 0 ]ʷ • [ 1 ]ʷ) ([ 2 ]ʷ • ([ 3 ]ʷ • ([ 1 ]ʷ • [ 0 ]ʷ • [ 1 ]ʷ) • [ 3 ]ʷ) • [ 2 ]ʷ)
    ∷ []

  all337 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all337 = Eq.refl

d337r : ∀ (b c : Bool) → Evaluated (U₄ b • G2 c) (G2 c • U₄ b)
d337r true true = fam-eval F E all337 0
d337r true false = fam-eval F E all337 1
d337r false true = fam-eval F E all337 2
d337r false false = fam-eval F E all337 3
