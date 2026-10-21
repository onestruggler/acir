------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-wire steps of rule (46), decided (Clément, Lemma 8.8)
--
-- `bb` is the box on wire 3 of the bottom four wires, controlled by the
-- wires 0 1 2 (every other wire idle); `b₁₀`, `b₀₁`, `b₀₀` are it negated
-- on the wire 2, 0, or both.  Between P ⊗ P on the wires 0 1, the CH
-- from wire 2 negated onto wire 1 and the CH from wire 1 onto wire 2 are
-- ζ and η, and their product splits over the colour of wire 0 into Vo
-- (white) and Vc (black), each a word in those boxes (`e-ζη`, `e-Vc`).
-- `πa`, `πb` carry the box's wire 3 to wire 0 and the wires 2 (resp. 1)
-- 0 1 (resp. 2) to 1 2 3: they turn the frames of the endgame into
-- those of (339) (Col.Hg₃, P₁₃) and of (336).  Used by GeneralN.Canon46b.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base46 where

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

------------------------------------------------------------------------
-- The words

πa πa′ πb πb′ : Circuit 4
πa  = Ex ↑ • Ex • Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑
πa′ = Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑ • Ex • Ex ↑
πb  = Ex ↑ • Ex • Ex ↑ • Ex ↑ ↑
πb′ = Ex ↑ ↑ • Ex ↑ • Ex • Ex ↑

bb b₁₀ b₀₁ b₀₀ : Circuit 4
bb  = (Ex ↑ ↑ • Ex ↑ • Ex) • Λ□ 3 • (Ex • Ex ↑ • Ex ↑ ↑)
b₁₀ = X ↑ ↑ • bb • X ↑ ↑
b₀₁ = X • bb • X
b₀₀ = X • b₁₀ • X

ζ η Vo Vc Vo′ : Circuit 4
ζ   = X ↑ ↑ • CZ ↑ • X ↑ ↑
η   = PP ↑ • CZ ↑ • PP ↑
Vo  = b₀₀ • (PP ↑ • b₀₁ • PP ↑)
Vc  = b₁₀ • (PP ↑ • bb • PP ↑)
Vo′ = (PP ↑ • b₀₁ • PP ↑) • b₀₀

------------------------------------------------------------------------
-- The splitting over wire 0

-- Every equation of this module is one family over shared factors,
-- each read once (ProdEval): bb is the box between swaps, so the box is
-- read once for all of them, and the relabellings below are products
-- of swaps, X and P ⊗ P.  Read word by word, they took 4.6 s.
private
  F : List (Circuit 4)
  F = Ex ↑ ∷ Ex ∷ Ex ↑ ↑ ∷ X ↑ ↑ ∷ X ∷ CZ ↑ ∷ PP ↑ ∷ Λ□ 3 ∷ X ↑ ∷ X ↑ ↑ ↑ ∷ P₁₃ ∷ []

  ex₁ ex ex₂ bbᵉ x₂ x cz pp box x₁ x₃ p₁₃ : Word ℕ
  ex₁ = [ 0 ]ʷ
  ex  = [ 1 ]ʷ
  ex₂ = [ 2 ]ʷ
  x₂  = [ 3 ]ʷ
  x   = [ 4 ]ʷ
  cz  = [ 5 ]ʷ
  pp  = [ 6 ]ʷ
  box = [ 7 ]ʷ
  x₁  = [ 8 ]ʷ
  x₃  = [ 9 ]ʷ
  p₁₃ = [ 10 ]ʷ
  bbᵉ = (ex₂ • ex₁ • ex) • box • (ex • ex₁ • ex₂)

  πaᵉ πa′ᵉ πbᵉ πb′ᵉ b₁₀ᵉ b₀₁ᵉ b₀₀ᵉ ζᵉ ηᵉ Voᵉ Vcᵉ Vo′ᵉ : Word ℕ
  πaᵉ  = ex₁ • ex • ex₂ • ex₁ • ex₂
  πa′ᵉ = ex₂ • ex₁ • ex₂ • ex • ex₁
  πbᵉ  = ex₁ • ex • ex₁ • ex₂
  πb′ᵉ = ex₂ • ex₁ • ex • ex₁
  b₁₀ᵉ = x₂ • bbᵉ • x₂
  b₀₁ᵉ = x • bbᵉ • x
  b₀₀ᵉ = x • b₁₀ᵉ • x
  ζᵉ   = x₂ • cz • x₂
  ηᵉ   = pp • cz • pp
  Voᵉ  = b₀₀ᵉ • (pp • b₀₁ᵉ • pp)
  Vcᵉ  = b₁₀ᵉ • (pp • bbᵉ • pp)
  Vo′ᵉ = (pp • b₀₁ᵉ • pp) • b₀₀ᵉ

  E : List (Word ℕ × Word ℕ)
  E = (ζᵉ • ηᵉ , Voᵉ • Vcᵉ)
    ∷ (Vcᵉ • ηᵉ • ζᵉ , Vo′ᵉ)
    ∷ (πaᵉ • bbᵉ • πa′ᵉ , box)
    ∷ (πbᵉ • bbᵉ • πb′ᵉ , box)
    ∷ (πaᵉ • πa′ᵉ , ε) ∷ (πa′ᵉ • πaᵉ , ε) ∷ (πbᵉ • πb′ᵉ , ε) ∷ (πb′ᵉ • πbᵉ , ε)
    ∷ (πaᵉ • x • πa′ᵉ , x₂) ∷ (πaᵉ • x₁ • πa′ᵉ , x₃) ∷ (πaᵉ • pp • πa′ᵉ , p₁₃)
    ∷ (πaᵉ • (ex₁ • ex) , ex • (ex₁ • ex₂)) ∷ ((ex • ex₁) • πa′ᵉ , (ex₂ • ex₁) • ex)
    ∷ (πbᵉ • x • πb′ᵉ , x₂) ∷ (πbᵉ • x₂ • πb′ᵉ , x₃) ∷ (πbᵉ • pp • πb′ᵉ , p₁₃)
    ∷ (πbᵉ • ex , ex • (ex₁ • ex₂)) ∷ (ex • πb′ᵉ , (ex₂ • ex₁) • ex)
    ∷ (x₂ • p₁₃ , p₁₃ • x₂)
    ∷ []

  all46 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all46 = Eq.refl

e-ζη : Evaluated (ζ • η) (Vo • Vc)
e-ζη = fam-eval F E all46 0

e-Vc : Evaluated (Vc • η • ζ) Vo′
e-Vc = fam-eval F E all46 1

------------------------------------------------------------------------
-- The two relabellings

ea₁ : Evaluated (πa • πa′) ε
ea₁ = fam-eval F E all46 4

ea₂ : Evaluated (πa′ • πa) ε
ea₂ = fam-eval F E all46 5

eb₁ : Evaluated (πb • πb′) ε
eb₁ = fam-eval F E all46 6

eb₂ : Evaluated (πb′ • πb) ε
eb₂ = fam-eval F E all46 7

ea-bb : Evaluated (πa • bb • πa′) (Λ□ 3)
ea-bb = fam-eval F E all46 2

eb-bb : Evaluated (πb • bb • πb′) (Λ□ 3)
eb-bb = fam-eval F E all46 3

ea-X : Evaluated (πa • X • πa′) (X ↑ ↑)
ea-X = fam-eval F E all46 8

ea-X₁ : Evaluated (πa • X ↑ • πa′) (X ↑ ↑ ↑)
ea-X₁ = fam-eval F E all46 9

ea-P : Evaluated (πa • PP ↑ • πa′) P₁₃
ea-P = fam-eval F E all46 10

ea-L : Evaluated (πa • (Ex ↑ • Ex)) (Ex • (Ex ↑ • Ex ↑ ↑))
ea-L = fam-eval F E all46 11

ea-R : Evaluated ((Ex • Ex ↑) • πa′) ((Ex ↑ ↑ • Ex ↑) • Ex)
ea-R = fam-eval F E all46 12

eb-X : Evaluated (πb • X • πb′) (X ↑ ↑)
eb-X = fam-eval F E all46 13

eb-X₂ : Evaluated (πb • X ↑ ↑ • πb′) (X ↑ ↑ ↑)
eb-X₂ = fam-eval F E all46 14

eb-P : Evaluated (πb • PP ↑ • πb′) P₁₃
eb-P = fam-eval F E all46 15

eb-L : Evaluated (πb • Ex) (Ex • (Ex ↑ • Ex ↑ ↑))
eb-L = fam-eval F E all46 16

eb-R : Evaluated (Ex • πb′) ((Ex ↑ ↑ • Ex ↑) • Ex)
eb-R = fam-eval F E all46 17

-- X on wire 2 passes P ⊗ P on the wires 1 3.
e-X₂P : Evaluated {4} (X ↑ ↑ • P₁₃) (P₁₃ • X ↑ ↑)
e-X₂P = fam-eval F E all46 18
