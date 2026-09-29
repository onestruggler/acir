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
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
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

e-ζη : Evaluated (ζ • η) (Vo • Vc)
e-ζη = evaluated Eq.refl

e-Vc : Evaluated (Vc • η • ζ) Vo′
e-Vc = evaluated Eq.refl

------------------------------------------------------------------------
-- The two relabellings

ea₁ : Evaluated (πa • πa′) ε
ea₁ = evaluated Eq.refl

ea₂ : Evaluated (πa′ • πa) ε
ea₂ = evaluated Eq.refl

eb₁ : Evaluated (πb • πb′) ε
eb₁ = evaluated Eq.refl

eb₂ : Evaluated (πb′ • πb) ε
eb₂ = evaluated Eq.refl

ea-bb : Evaluated (πa • bb • πa′) (Λ□ 3)
ea-bb = evaluated Eq.refl

eb-bb : Evaluated (πb • bb • πb′) (Λ□ 3)
eb-bb = evaluated Eq.refl

ea-X : Evaluated (πa • X • πa′) (X ↑ ↑)
ea-X = evaluated Eq.refl

ea-X₁ : Evaluated (πa • X ↑ • πa′) (X ↑ ↑ ↑)
ea-X₁ = evaluated Eq.refl

ea-P : Evaluated (πa • PP ↑ • πa′) P₁₃
ea-P = evaluated Eq.refl

ea-L : Evaluated (πa • (Ex ↑ • Ex)) (Ex • (Ex ↑ • Ex ↑ ↑))
ea-L = evaluated Eq.refl

ea-R : Evaluated ((Ex • Ex ↑) • πa′) ((Ex ↑ ↑ • Ex ↑) • Ex)
ea-R = evaluated Eq.refl

eb-X : Evaluated (πb • X • πb′) (X ↑ ↑)
eb-X = evaluated Eq.refl

eb-X₂ : Evaluated (πb • X ↑ ↑ • πb′) (X ↑ ↑ ↑)
eb-X₂ = evaluated Eq.refl

eb-P : Evaluated (πb • PP ↑ • πb′) P₁₃
eb-P = evaluated Eq.refl

eb-L : Evaluated (πb • Ex) (Ex • (Ex ↑ • Ex ↑ ↑))
eb-L = evaluated Eq.refl

eb-R : Evaluated (Ex • πb′) ((Ex ↑ ↑ • Ex ↑) • Ex)
eb-R = evaluated Eq.refl

-- X on wire 2 passes P ⊗ P on the wires 1 3.
e-X₂P : Evaluated {4} (X ↑ ↑ • P₁₃) (P₁₃ • X ↑ ↑)
e-X₂P = evaluated Eq.refl
