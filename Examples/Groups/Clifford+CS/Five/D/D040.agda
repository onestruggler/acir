{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD040 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D040 (Sᴰ : SD040) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ014-CX23 : Ws → St 893
  lem-comm-CCZ014-CX23 = pickᴰ 0 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 1 Sᴰ
  lem-comm-TOFF013-CX24 : Ws → St 1059
  lem-comm-TOFF013-CX24 = pickᴰ 2 Sᴰ
  lem-comm-TOFF023-CX14 : Ws → St 1060
  lem-comm-TOFF023-CX14 = pickᴰ 3 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 4 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 5 Sᴰ
  lem-box-perm-1324-at243243 : Ws → St 1256
  lem-box-perm-1324-at243243 = pickᴰ 6 Sᴰ
  lem-box2-at122441 : Ws → St 1259
  lem-box2-at122441 = pickᴰ 7 Sᴰ
  lem-box-perm-1324-at3443 : Ws → St 1354
  lem-box-perm-1324-at3443 = pickᴰ 8 Sᴰ
  lem-box-perm-1423-at243243 : Ws → St 1497
  lem-box-perm-1423-at243243 = pickᴰ 9 Sᴰ
  lem-box-perm-3241-at243243 : Ws → St 1519
  lem-box-perm-3241-at243243 = pickᴰ 10 Sᴰ
  lem-S2-SBOX⟨0·1·42·3⟩ : Ws → St 1523
  lem-S2-SBOX⟨0·1·42·3⟩ = pickᴰ 11 Sᴰ
  lem-S2-SBOX⟨0·2·43·1⟩ : Ws → St 1524
  lem-S2-SBOX⟨0·2·43·1⟩ = pickᴰ 12 Sᴰ
  lem-CKc-box-at233442 : Ws → St 1535
  lem-CKc-box-at233442 = pickᴰ 13 Sᴰ
  lem-box-perm-1342-at233442 : Ws → St 1538
  lem-box-perm-1342-at233442 = pickᴰ 14 Sᴰ
  lem-CKc-box-at3443 : Ws → St 1547
  lem-CKc-box-at3443 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 843 c4
  q3 : Ws → Eqn
  q3 c4 = wpE 845 c4
  q4 : Ws → Eqn
  q4 c4 = wlE 241 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wpE 89 c4
  q6 : Ws → Eqn
  q6 c4 = wpE 36 c4
  q7 : Ws → Eqn
  q7 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 35 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 34 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 88 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 97 c4
  q12 : Ws → Eqn
  q12 c4 = wlE 245 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 95 c4
  q14 : Ws → Eqn
  q14 c4 = sE 1059 (lem-comm-TOFF013-CX24 c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 94 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 246 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 842 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 90 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 247 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 81 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 244 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 87 c4
  q23 : Ws → Eqn
  q23 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 805 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 806 c4
  q26 : Ws → Eqn
  q26 c4 = wlE 217 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 65 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 64 c4
  q29 : Ws → Eqn
  q29 c4 = sE 893 (lem-comm-CCZ014-CX23 c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 63 c4
  q31 : Ws → Eqn
  q31 c4 = wpE 62 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 61 c4
  q33 : Ws → Eqn
  q33 c4 = wpE 72 c4
  q34 : Ws → Eqn
  q34 c4 = wlE 220 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wpE 70 c4
  q36 : Ws → Eqn
  q36 c4 = sE 1060 (lem-comm-TOFF023-CX14 c4)
  q37 : Ws → Eqn
  q37 c4 = wpE 69 c4
  q38 : Ws → Eqn
  q38 c4 = wlE 221 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 74 c4
  q40 : Ws → Eqn
  q40 c4 = wpE 66 c4
  q41 : Ws → Eqn
  q41 c4 = wlE 222 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wpE 53 c4
  q43 : Ws → Eqn
  q43 c4 = wlE 219 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wpE 60 c4
  q45 : Ws → Eqn
  q45 c4 = wpE 278 c4
  q46 : Ws → Eqn
  q46 c4 = wlE 274 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 1013 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 735 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 725 c4
  q50 : Ws → Eqn
  q50 c4 = wpE 823 c4
  q51 : Ws → Eqn
  q51 c4 = wlE 1014 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1044 c4
  q53 : Ws → Eqn
  q53 c4 = wpE 1045 c4
  q54 : Ws → Eqn
  q54 c4 = wpE 124 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 836 c4
  q56 : Ws → Eqn
  q56 c4 = wpE 67 c4
  q57 : Ws → Eqn
  q57 c4 = wlE 1017 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = wpE 265 c4
  q59 : Ws → Eqn
  q59 c4 = sE 1519 (lem-box-perm-3241-at243243 c4)
  q60 : Ws → Eqn
  q60 c4 = sE 1259 (lem-box2-at122441 c4)
  q61 : Ws → Eqn
  q61 c4 = wlE 1000 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 263 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wlE 413 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 305 (lit c4)

-- nf-comm-CSu-CS@1: 282 steps
lem-nf-comm-CSu-CSat1 : Ws → ⟪ (ℓ "侧侬") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏亭乇亭么") ⟫ʷ
lem-nf-comm-CSu-CSat1 c4 = derive (ℓ "侧侬") (ℓ "亲乎亲乏亭乇亭么")
  (re 0 1 (ℓ "仄亲侥亲侦") ∷
   re 2 1 (ℓ "乎") ∷
   re 4 1 (ℓ "乏") ∷
   re 5 1 (ℓ "仞亭侪亭侫") ∷
   re 7 1 (ℓ "乇") ∷
   re 9 1 (ℓ "么") ∷
   rw 5 (q1 c4) ∷
   rw 8 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 9 (q4 c4) ∷
   rw 6 (q11 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q14 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 9 (q20 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw 7 (q20 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 11 (q2 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 12 (q4 c4) ∷
   rw 9 (q11 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw 10 (q22 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 0 (q23 c4) ∷
   rw 3 (q24 c4) ∷
   rw 2 (q25 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q28 c4) ∷
   rw 6 (q29 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q29 c4) ∷
   rw 9 (q31 c4) ∷
   rw 10 (q32 c4) ∷
   rw 4 (q26 c4) ∷
   rw 1 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 3 (q24 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw 0 (q40 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   rw 2 (q23 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 3 (q23 c4) ∷
   rw 6 (q24 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw 7 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 10 (q30 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q31 c4) ∷
   rw 13 (q32 c4) ∷
   rw 7 (q26 c4) ∷
   rw 4 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw 6 (q36 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q28 c4) ∷
   rw 6 (q29 c4) ∷
   rw 7 (q30 c4) ∷
   rw 8 (q29 c4) ∷
   rw 9 (q31 c4) ∷
   rw 10 (q32 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 8 (q43 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 6 (q43 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 9 (q45 c4) ∷
   rw 9 (q46 c4) ∷
   rw 8 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 10 (q30 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw 6 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw 8 (q30 c4) ∷
   rw 9 (q29 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 11 (q47 c4) ∷
   rw⁻ 10 (q48 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw 12 (q36 c4) ∷
   rw⁻ 13 (q50 c4) ∷
   rw 14 (q36 c4) ∷
   rw⁻ 15 (q41 c4) ∷
   rw⁻ 16 (q51 c4) ∷
   rw 10 (q47 c4) ∷
   rw 9 (q52 c4) ∷
   rw⁻ 9 (q47 c4) ∷
   rw⁻ 8 (q48 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw 10 (q36 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 12 (q36 c4) ∷
   rw⁻ 13 (q41 c4) ∷
   rw⁻ 14 (q51 c4) ∷
   rw 8 (q47 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw 7 (q52 c4) ∷
   rw 9 (q54 c4) ∷
   rw 11 (q46 c4) ∷
   rw 10 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q30 c4) ∷
   rw 13 (q29 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 10 (q46 c4) ∷
   rw 7 (q55 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 12 (q38 c4) ∷
   rw 11 (q56 c4) ∷
   rw⁻ 10 (q38 c4) ∷
   rw 9 (q56 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw 10 (q23 c4) ∷
   rw⁻ 13 (q45 c4) ∷
   rw 13 (q46 c4) ∷
   rw 12 (q28 c4) ∷
   rw 13 (q29 c4) ∷
   rw 14 (q30 c4) ∷
   rw 15 (q29 c4) ∷
   rw 16 (q31 c4) ∷
   rw⁻ 12 (q46 c4) ∷
   rw⁻ 11 (q45 c4) ∷
   rw 11 (q46 c4) ∷
   rw 10 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q30 c4) ∷
   rw 13 (q29 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 10 (q46 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 15 (q47 c4) ∷
   rw⁻ 14 (q48 c4) ∷
   rw⁻ 15 (q49 c4) ∷
   rw 16 (q36 c4) ∷
   rw⁻ 17 (q50 c4) ∷
   rw 18 (q36 c4) ∷
   rw⁻ 19 (q41 c4) ∷
   rw⁻ 20 (q51 c4) ∷
   rw 14 (q47 c4) ∷
   rw 13 (q52 c4) ∷
   rw⁻ 13 (q47 c4) ∷
   rw⁻ 12 (q48 c4) ∷
   rw⁻ 13 (q49 c4) ∷
   rw 14 (q36 c4) ∷
   rw⁻ 15 (q50 c4) ∷
   rw 16 (q36 c4) ∷
   rw⁻ 17 (q41 c4) ∷
   rw⁻ 18 (q51 c4) ∷
   rw 12 (q47 c4) ∷
   rw⁻ 13 (q53 c4) ∷
   rw 11 (q52 c4) ∷
   rw 13 (q54 c4) ∷
   rw 15 (q46 c4) ∷
   rw 14 (q28 c4) ∷
   rw 15 (q29 c4) ∷
   rw 16 (q30 c4) ∷
   rw 17 (q29 c4) ∷
   rw 18 (q31 c4) ∷
   rw⁻ 14 (q46 c4) ∷
   rw 11 (q55 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw 13 (q23 c4) ∷
   rw⁻ 16 (q57 c4) ∷
   rw 15 (q58 c4) ∷
   rw⁻ 14 (q57 c4) ∷
   rw 13 (q58 c4) ∷
   rw⁻ 14 (q23 c4) ∷
   rw 14 (q59 c4) ∷
   rw 14 (q60 c4) ∷
   rw 0 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw 6 (q63 c4) ∷
   rw 7 (q64 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = sE 1524 (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 1285 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = sE 1497 (lem-box-perm-1423-at243243 c4)
  q68 : Ws → Eqn
  q68 c4 = sE 1535 (lem-CKc-box-at233442 c4)
  q69 : Ws → Eqn
  q69 c4 = sE 1538 (lem-box-perm-1342-at233442 c4)
  q70 : Ws → Eqn
  q70 c4 = wpE 632 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 633 c4
  q72 : Ws → Eqn
  q72 c4 = sE 1256 (lem-box-perm-1324-at243243 c4)
  q73 : Ws → Eqn
  q73 c4 = sE 1547 (lem-CKc-box-at3443 c4)
  q74 : Ws → Eqn
  q74 c4 = sE 1354 (lem-box-perm-1324-at3443 c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 508 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 181 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 1286 (lit c4)

-- nf-rel-266@1: 154 steps
lem-nf-rel-266at1 : Ws → ⟪ (ℓ "亊侬侬亊丢亇侬侬亇丢侧亇侬侬亇丢亊侬侬亊丢") ⟫ʷ ≈ ⟪ (ℓ "亲亱亲乎亲乏交亇亰亇丢亊亰亊交丢仄") ⟫ʷ
lem-nf-rel-266at1 c4 = derive (ℓ "亊侬侬亊丢亇侬侬亇丢侧亇侬侬亇丢亊侬侬亊丢") (ℓ "亲亱亲乎亲乏交亇亰亇丢亊亰亊交丢仄")
  (rw 1 (q65 c4) ∷
   rw 5 (q65 c4) ∷
   rw 10 (q65 c4) ∷
   rw 14 (q65 c4) ∷
   re 8 1 (ℓ "仄亲侥亲侦") ∷
   re 10 1 (ℓ "乎") ∷
   re 12 1 (ℓ "乏") ∷
   rw 0 (q66 c4) ∷
   rw 2 (q23 c4) ∷
   rw 5 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw 6 (q27 c4) ∷
   rw 7 (q28 c4) ∷
   rw 8 (q29 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q29 c4) ∷
   rw 11 (q31 c4) ∷
   rw 12 (q32 c4) ∷
   rw 6 (q26 c4) ∷
   rw 3 (q33 c4) ∷
   rw 5 (q34 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 7 (q36 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q24 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 3 (q27 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw 7 (q29 c4) ∷
   rw 8 (q31 c4) ∷
   rw 9 (q32 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 4 (q23 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 5 (q23 c4) ∷
   rw 8 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw 9 (q27 c4) ∷
   rw 10 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q30 c4) ∷
   rw 13 (q29 c4) ∷
   rw 14 (q31 c4) ∷
   rw 15 (q32 c4) ∷
   rw 9 (q26 c4) ∷
   rw 6 (q33 c4) ∷
   rw 8 (q34 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw 10 (q36 c4) ∷
   rw⁻ 11 (q38 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 8 (q24 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw 6 (q27 c4) ∷
   rw 7 (q28 c4) ∷
   rw 8 (q29 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q29 c4) ∷
   rw 11 (q31 c4) ∷
   rw 12 (q32 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 10 (q43 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 8 (q43 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw 8 (q67 c4) ∷
   rw 8 (q68 c4) ∷
   rw 11 (q69 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 14 (q45 c4) ∷
   rw 14 (q46 c4) ∷
   rw 13 (q28 c4) ∷
   rw 14 (q29 c4) ∷
   rw 15 (q30 c4) ∷
   rw 16 (q29 c4) ∷
   rw 17 (q31 c4) ∷
   rw⁻ 13 (q46 c4) ∷
   rw⁻ 12 (q45 c4) ∷
   rw 12 (q46 c4) ∷
   rw 11 (q28 c4) ∷
   rw 12 (q29 c4) ∷
   rw 13 (q30 c4) ∷
   rw 14 (q29 c4) ∷
   rw 15 (q31 c4) ∷
   rw⁻ 11 (q46 c4) ∷
   rw⁻ 12 (q23 c4) ∷
   rw 12 (q67 c4) ∷
   rw 12 (q68 c4) ∷
   rw 15 (q69 c4) ∷
   rw 15 (q23 c4) ∷
   rw⁻ 18 (q70 c4) ∷
   rw 17 (q71 c4) ∷
   rw⁻ 16 (q70 c4) ∷
   rw 15 (q71 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw 16 (q72 c4) ∷
   rw 16 (q73 c4) ∷
   rw 19 (q74 c4) ∷
   rw 19 (q23 c4) ∷
   rw⁻ 22 (q45 c4) ∷
   rw 22 (q46 c4) ∷
   rw 21 (q28 c4) ∷
   rw 22 (q29 c4) ∷
   rw 23 (q30 c4) ∷
   rw 24 (q29 c4) ∷
   rw 25 (q31 c4) ∷
   rw⁻ 21 (q46 c4) ∷
   rw⁻ 20 (q45 c4) ∷
   rw 20 (q46 c4) ∷
   rw 19 (q28 c4) ∷
   rw 20 (q29 c4) ∷
   rw 21 (q30 c4) ∷
   rw 22 (q29 c4) ∷
   rw 23 (q31 c4) ∷
   rw⁻ 19 (q46 c4) ∷
   rw⁻ 20 (q23 c4) ∷
   rw 20 (q72 c4) ∷
   rw 20 (q73 c4) ∷
   rw 23 (q74 c4) ∷
   rw 23 (q23 c4) ∷
   rw⁻ 26 (q70 c4) ∷
   rw 25 (q71 c4) ∷
   rw⁻ 24 (q70 c4) ∷
   rw 23 (q71 c4) ∷
   rw⁻ 24 (q23 c4) ∷
   rw 2 (q61 c4) ∷
   rw 4 (q62 c4) ∷
   rw 8 (q75 c4) ∷
   rw 9 (q76 c4) ∷
   rw 10 (q77 c4) ∷
   rw 11 (q76 c4) ∷
   rw 12 (q75 c4) ∷
   rw 13 (q76 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = sE 1523 (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q79 : Ws → Eqn
  q79 c4 = wlE 1289 (lit c4)

-- nf-rel-267@1: 5 steps
lem-nf-rel-267at1 : Ws → ⟪ (ℓ "亇侧侧亇丢侬侬亇侧侧亇丢侬侬") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
lem-nf-rel-267at1 c4 = derive (ℓ "亇侧侧亇丢侬侬亇侧侧亇丢侬侬") (ℓ "京")
  (rw 1 (q78 c4) ∷
   rw 4 (q65 c4) ∷
   rw 6 (q78 c4) ∷
   rw 9 (q65 c4) ∷
   rw⁻ 0 (q79 c4) ∷ []) Eq.refl
