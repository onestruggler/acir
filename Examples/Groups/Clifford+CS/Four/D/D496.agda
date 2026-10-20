{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D496 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00027 ; wn00031 ; wn00048 ; wn00065)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00317 ; wn00329)
open import Examples.Groups.Clifford+CS.Four.Wins.W10 using (wn00772)
open import Examples.Groups.Clifford+CS.Four.Wins.W20 using (wn01052 ; wn01053)
open import Examples.Groups.Clifford+CS.Four.Wins.W21 using (wn01106)
open import Examples.Groups.Clifford+CS.Four.Wins.W25 using (wn01252 ; wn01253 ; wn01254)
open import Examples.Groups.Clifford+CS.Four.Wins.W26 using (wn01308 ; wn01309)

-- Bar(SSKSKK;0,2->3) passes groups of WBar(SSKSKK;~0,1->3) part2: 51 steps
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part2 : ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  b0 = at 41 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 40 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 42 2 [] wn00003 ▸
       at 39 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 41 2 [] wn00003 ▸
       at 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 40 2 [] wn00003 ▸
       at 37 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  b1 = at 39 2 [] wn00003 ▸
       at 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 38 2 [] wn00003 ▸
       at 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 37 2 [] wn00003 ▸
       at 34 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 36 2 [] wn00003 ▸
       at 33 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  b2 = at 35 2 [] wn00003 ▸
       at 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 [] wn00003 ▸
       at 31 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 33 2 [] wn00003 ▸
       at 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 [] wn00003 ▸
       at 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  b3 = at 31 2 [] wn00003 ▸
       at 30 12 (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ []) wn01252 ▸
       at 31 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 29 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 32 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 30 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 33 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 31 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  b4 = at 34 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 32 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 35 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 33 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 36 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 34 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 37 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 35 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CK02 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  b5 = at 38 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 36 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 39 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 37 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 40 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 38 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 41 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 39 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CK02 ∷ Sw23 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  b6 = at 42 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 40 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 41 2 [] wn00003 ▸ done

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [X0 CK02 X0]: 251 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-CK02-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-CK02-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (run b31)))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ X0 ∷ CK13 ∷ CK02 ∷ X0 ∷ CK13 ∷ [])
  b0 = at 28 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 30 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 30 2 (CK01 ∷ CK23 ∷ []) (sym (low-comm (CK₀₁) (CK₀₁))) ▸
       at 31 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 29 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 27 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ X0 ∷ CK13 ∷ CK02 ∷ X0 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CK13 ∷ CK13 ∷ [])
  b1 = at 29 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 29 2 (CK01 ∷ CK23 ∷ []) (sym (low-comm (CK₀₁) (CK₀₁))) ▸
       at 30 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 28 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 26 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 28 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK23 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b2 = at 27 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 28 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 29 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 27 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 25 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 27 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸ done

  b3 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK23 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK01 ∷ CS23 ∷ Sw12 ∷ X0 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b3 = at 27 2 (CK01 ∷ CK23 ∷ []) (sym (low-comm (CK₀₁) (CK₀₁))) ▸
       at 28 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 26 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 24 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 26 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 26 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸ done

  b4 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK01 ∷ CS23 ∷ Sw12 ∷ X0 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ X0 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b4 = at 27 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 25 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 23 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 25 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 25 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 26 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸ done

  b5 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ X0 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ CS13 ∷ X0 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b5 = at 24 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 22 4 (X0 ∷ CK02 ∷ X0 ∷ CX01 ∷ []) wn01253 ▸
       at 21 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 23 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 23 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 24 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸ done

  b6 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ CS13 ∷ X0 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK02 ∷ CS13 ∷ X0 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b6 = at 22 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 20 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 22 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 22 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 23 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 21 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK02 ∷ CS13 ∷ X0 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK02 ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b7 = at 22 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 19 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 21 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 21 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 22 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 20 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸ done

  b8 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK02 ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK02 ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b8 = at 18 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 20 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 20 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 21 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 19 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 17 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸ done

  b9 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK02 ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b9 = at 19 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 19 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 20 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 18 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 16 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 18 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ X0 ∷ CK02 ∷ X0 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b10 = at 17 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 18 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 19 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 17 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 15 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 16 2 (CK02 ∷ S1 ∷ []) wn01254 ▸
       at 17 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸ done

  b11 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ X0 ∷ CK02 ∷ X0 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK02 ∷ X0 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b11 = at 14 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 16 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 16 2 (CK01 ∷ CK23 ∷ []) (sym (low-comm (CK₀₁) (CK₀₁))) ▸
       at 17 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 15 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 13 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸ done

  b12 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK02 ∷ X0 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b12 = at 15 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 15 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 16 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 14 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 12 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 14 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ X0 ∷ Sw12 ∷ CS23 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b13 = at 13 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 14 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 15 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 13 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 11 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 13 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸ done

  b14 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ X0 ∷ Sw12 ∷ CS23 ∷ CK01 ∷ Sw12 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ X0 ∷ CK13 ∷ CK02 ∷ X0 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b14 = at 13 2 (CK01 ∷ CS23 ∷ []) (sym (low-comm (CK₀₁) (CS))) ▸
       at 14 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 12 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 10 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 11 2 (CK02 ∷ S1 ∷ []) wn01254 ▸
       at 12 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 9 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸ done

  b15 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ X0 ∷ CK13 ∷ CK02 ∷ X0 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ X0 ∷ CK02 ∷ S1 ∷ X0 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b15 = at 11 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 11 2 (CK01 ∷ CK23 ∷ []) (sym (low-comm (CK₀₁) (CK₀₁))) ▸
       at 12 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 10 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 8 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 9 2 (CK02 ∷ S1 ∷ []) wn01254 ▸ done

  b16 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ X0 ∷ CK02 ∷ S1 ∷ X0 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ X0 ∷ CK02 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b16 = at 10 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 7 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 9 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 9 2 (CK01 ∷ CK23 ∷ []) (sym (low-comm (CK₀₁) (CK₀₁))) ▸
       at 10 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 8 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸ done

  b17 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ X0 ∷ CK02 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ Sw01 ∷ CK12 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b17 = at 6 4 (X0 ∷ CK02 ∷ X0 ∷ CX01 ∷ []) wn01253 ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 7 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 6 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸ done

  b18 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ Sw01 ∷ CK12 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ Sw23 ∷ Sw01 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b18 = at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 4 (X1 ∷ CK12 ∷ X1 ∷ CK13 ∷ []) wn01308 ▸
       at 5 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 6 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 7 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b19 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ Sw23 ∷ Sw01 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b19 = at 9 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 6 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 5 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸ done

  b20 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ X0 ∷ CK02 ∷ Sw01 ∷ X1 ∷ CK13 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b20 = at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 4 (X1 ∷ CK12 ∷ X1 ∷ CK13 ∷ []) wn01308 ▸
       at 4 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 5 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸ done

  b21 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ X0 ∷ CK02 ∷ Sw01 ∷ X1 ∷ CK13 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ X0 ∷ CK02 ∷ X0 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b21 = at 6 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b22 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ X0 ∷ CK02 ∷ X0 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ CS13 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b22 = at 6 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 5 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 4 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ CS13 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b23 = at 4 4 (X1 ∷ CK12 ∷ X1 ∷ CS13 ∷ []) wn01309 ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 4 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 5 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b24 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b24 = at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 4 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 3 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b25 : Chain (CS03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ X0 ∷ CK02 ∷ X0 ∷ Sw01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b25 = at 3 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 4 (X1 ∷ CK12 ∷ X1 ∷ CK13 ∷ []) wn01308 ▸
       at 2 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 3 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 4 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b26 : Chain (CS03 ∷ CS03 ∷ X0 ∷ CK02 ∷ X0 ∷ Sw01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ X0 ∷ Sw01 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b26 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 3 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸ done

  b27 : Chain (CS03 ∷ CS03 ∷ X0 ∷ Sw01 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ X0 ∷ Sw01 ∷ CK12 ∷ X1 ∷ CS13 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b27 = at 2 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 4 (X1 ∷ CK12 ∷ X1 ∷ CS13 ∷ []) wn01309 ▸
       at 1 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸ done

  b28 : Chain (CS03 ∷ X0 ∷ Sw01 ∷ CK12 ∷ X1 ∷ CS13 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b28 = at 2 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸ done

  b29 : Chain (CS03 ∷ X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b29 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 2 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 1 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b30 : Chain (Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X1 ∷ CK12 ∷ X1 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b30 = at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 4 (X1 ∷ CK12 ∷ X1 ∷ CS13 ∷ []) wn01309 ▸
       at 0 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 1 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 2 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b31 : Chain (X0 ∷ CK02 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b31 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸ done
