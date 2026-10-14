------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire evaluations for rule (38) (GeneralN.Canon38)
--
-- c is the CH from wire 2 onto wire 3 and Q the negations of the wires
-- 2 3.  The letters of (320) on the wires 0–3 — the triply controlled
-- ZX and XZ on wire 0 and on wire 1 — pass c once coloured white on the
-- wires 2 3 (`e-ZX`, `e-XZ`, `e-Kb`, `e-Kb′`); c with its control
-- negated is the CH from wire 3 onto wire 1, white, under the swaps of
-- the wires 2 3 and 1 2 (`e-°c`); and c is the CH from wire 2 onto
-- wire 0 under the transposition of the wires 0 3 (`e-pc`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base38 where

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

c₄ Q₄ : Circuit 4
c₄ = (Ex • CH • Ex) ↑ ↑
Q₄ = X ↑ ↑ • X ↑ ↑ ↑

-- One family over shared factors, each read once (ProdEval).
private
  F : List (Circuit 4)
  F = c₄ ∷ Q₄ ∷ ΛZX 3 ∷ ΛXZ 3 ∷ Ex ∷ X ↑ ↑ ∷ Ex ↑ ↑ ∷ Ex ↑ ∷ (Ex ↑ • °CH • Ex ↑) ↑ ∷ CH ∷ []

  c q zx xz ex x₂ ex₂ ex₁ ch : Word ℕ
  c   = [ 0 ]ʷ
  q   = [ 1 ]ʷ
  zx  = [ 2 ]ʷ
  xz  = [ 3 ]ʷ
  ex  = [ 4 ]ʷ
  x₂  = [ 5 ]ʷ
  ex₂ = [ 6 ]ʷ
  ex₁ = [ 7 ]ʷ
  ch  = [ 9 ]ʷ

  -- c₄ against a gate between the two Q₄.
  comm : Word ℕ → Word ℕ × Word ℕ
  comm g = c • (q • g • q) , (q • g • q) • c

  E : List (Word ℕ × Word ℕ)
  E = comm zx ∷ comm xz ∷ comm (ex • zx • ex) ∷ comm (ex • xz • ex)
    ∷ (x₂ • c • x₂ , (ex₂ • ex₁) • [ 8 ]ʷ • (ex₁ • ex₂))
    ∷ ((ex • (ex₁ • (ex₂ • (ex₁ • ex)))) • (ex₁ • ch • ex₁) • ((((ex • ex₁) • ex₂) • ex₁) • ex) , c)
    ∷ []

  all38 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all38 = Eq.refl

e-ZX : Evaluated {4} (c₄ • (Q₄ • ΛZX 3 • Q₄)) ((Q₄ • ΛZX 3 • Q₄) • c₄)
e-ZX = fam-eval F E all38 0

e-XZ : Evaluated {4} (c₄ • (Q₄ • ΛXZ 3 • Q₄)) ((Q₄ • ΛXZ 3 • Q₄) • c₄)
e-XZ = fam-eval F E all38 1

e-Kb : Evaluated {4} (c₄ • (Q₄ • (Ex • ΛZX 3 • Ex) • Q₄)) ((Q₄ • (Ex • ΛZX 3 • Ex) • Q₄) • c₄)
e-Kb = fam-eval F E all38 2

e-Kb′ : Evaluated {4} (c₄ • (Q₄ • (Ex • ΛXZ 3 • Ex) • Q₄)) ((Q₄ • (Ex • ΛXZ 3 • Ex) • Q₄) • c₄)
e-Kb′ = fam-eval F E all38 3

e-°c : Evaluated {4} (X ↑ ↑ • c₄ • X ↑ ↑) ((Ex ↑ ↑ • Ex ↑) • (Ex ↑ • °CH • Ex ↑) ↑ • (Ex ↑ • Ex ↑ ↑))
e-°c = fam-eval F E all38 4

e-pc : Evaluated {4} ((Ex • (Ex ↑ • (Ex ↑ ↑ • (Ex ↑ • Ex)))) • (Ex ↑ • CH • Ex ↑) • ((((Ex • Ex ↑) • Ex ↑ ↑) • Ex ↑) • Ex)) c₄
e-pc = fam-eval F E all38 5
