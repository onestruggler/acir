{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD034 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D034 (Sᴰ : SD034) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CX20-TOFF413)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-cP-at04122041 : Ws → St 1019
  lem-box-cP-at04122041 = pickᴰ 0 Sᴰ
  lem-box2-at04122041 : Ws → St 1250
  lem-box2-at04122041 = pickᴰ 1 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1019 (lem-box-cP-at04122041 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 87 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 1544 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1545 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wpE 88 c4
  q6 : Ws → Eqn
  q6 c4 = wpE 39 c4
  q7 : Ws → Eqn
  q7 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = wpE 32 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 21 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 89 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 1373 c4
  q12 : Ws → Eqn
  q12 c4 = wpE 1374 c4
  q13 : Ws → Eqn
  q13 c4 = wlE 1270 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1546 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CX20 ∷ Toff413 ∷ []) (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = wpE 1375 c4
  q17 : Ws → Eqn
  q17 c4 = wpE 1376 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 1377 c4
  q19 : Ws → Eqn
  q19 c4 = wpE 1378 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 81 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 1547 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1250 (lem-box2-at04122041 c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 1549 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 204 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 1705 (lit c4)

-- S2-SBOX(0;2;43;1) @0440: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at0440 : Ws → ⟪ (Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4 = derive (Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ []) (CCZ023 ∷ [])
  (re 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   re 0 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q13 c4) ∷
   rw 11 (q14 c4) ∷
   rw 10 (q15 c4) ∷
   rw 9 (q16 c4) ∷
   rw 8 (q15 c4) ∷
   rw 7 (q17 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 2 (q4 c4) ∷
   rw 2 (q11 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 6 (q11 c4) ∷
   rw 5 (q13 c4) ∷
   rw 9 (q14 c4) ∷
   rw 8 (q15 c4) ∷
   rw 7 (q16 c4) ∷
   rw 6 (q15 c4) ∷
   rw 5 (q17 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw 0 (q22 c4) ∷
   rw 0 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 0 (q25 c4) ∷ []) Eq.refl
