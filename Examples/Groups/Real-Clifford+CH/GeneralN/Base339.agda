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
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; Hg₃ ; P₁₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base322 using (N3F)

d339 : ∀ (a : Bool) →
       Evaluated (col (true ∷ true ∷ true ∷ a ∷ []) (Λ□ 3) • col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0))
                 (col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0) • col (true ∷ true ∷ true ∷ a ∷ []) (Λ□ 3))
d339 true  = evaluated Eq.refl
d339 false = evaluated Eq.refl

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

d339r : ∀ (a b c : Bool) → Evaluated (G1r a b • G2r c) (G2r c • G1r a b)
d339r true  true  true  = evaluated Eq.refl
d339r true  true  false = evaluated Eq.refl
d339r true  false true  = evaluated Eq.refl
d339r true  false false = evaluated Eq.refl
d339r false true  true  = evaluated Eq.refl
d339r false true  false = evaluated Eq.refl
d339r false false true  = evaluated Eq.refl
d339r false false false = evaluated Eq.refl
