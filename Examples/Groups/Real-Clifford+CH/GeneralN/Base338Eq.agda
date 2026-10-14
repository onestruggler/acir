------------------------------------------------------------------------
-- Presentations of groups
--
-- The doubly controlled ZX between P ⊗ P against the box on wire 1
-- negated on wire 2, on four wires, decided (GeneralN.Box338Eq)
--
-- RW₄ is CCZX between P ⊗ P on the wires 0 1; Dw₄ the box on wire 1
-- controlled by wire 0, negatively by wire 2, and by wire 3.  They
-- commute (`d-base`), and RW₄ commutes with the two rotation letters of
-- (320) under the same conjugations (`d-zx`, `d-kb`): the base and the
-- letters of Box338Eq's induction.  Each an evaluation of a few
-- seconds; in a module of its own, since Agda frees the memory of an
-- evaluation only when its module is done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base338Eq where

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

-- CCZX between P ⊗ P.
RW₄ : Circuit 4
RW₄ = PP ↓ • CCZX • PP ↓

-- The swap of the wires 0 1 around X on wire 2 around w.
SN : Circuit 4 → Circuit 4
SN w = Ex ↓ • (X ↑ ↑ • w • X ↑ ↑) • Ex ↓

Dw₄ L-zx L-kb : Circuit 4
Dw₄  = SN (Λ□ 3)
L-zx = SN (ΛZX 3 ↓ᵏ 0)
L-kb = SN (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓)

-- The three commutations, one family over RW₄ and the three gates, each
-- read once (ProdEval).
private
  F : List (Circuit 4)
  F = RW₄ ∷ Dw₄ ∷ L-zx ∷ L-kb ∷ []

  comm : ℕ → Word ℕ × Word ℕ
  comm i = [ 0 ]ʷ • [ i ]ʷ , [ i ]ʷ • [ 0 ]ʷ

  E : List (Word ℕ × Word ℕ)
  E = comm 1 ∷ comm 2 ∷ comm 3 ∷ []

  all338Eq : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all338Eq = Eq.refl

d-base : Evaluated (RW₄ • Dw₄) (Dw₄ • RW₄)
d-base = fam-eval F E all338Eq 0

d-zx : Evaluated (RW₄ • L-zx) (L-zx • RW₄)
d-zx = fam-eval F E all338Eq 1

d-kb : Evaluated (RW₄ • L-kb) (L-kb • RW₄)
d-kb = fam-eval F E all338Eq 2
