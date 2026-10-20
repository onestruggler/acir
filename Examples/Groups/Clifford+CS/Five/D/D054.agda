{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D054 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-I-at0213243140 ; lem-F4-I-K3-at0213243140 ; lem-F4-I-S2-at0213243140 ; lem-F4-K3-I-at0213243140 ; lem-F4-K3-K3-at0213243140 ; lem-F4-K3-S2-at0213243140 ; lem-F4-S2-I-at0213243140 ; lem-F4-S2-K3-at0213243140 ; lem-F4-S2-S2-at0213243140)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-I-CS2-at0213243140 ; lem-F4-S2-CS2-at0213243140)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-F4-CS2-CS2-at0213243140 ; lem-F4-CS2-I-at0213243140 ; lem-F4-CS2-S2-at0213243140)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F5-23)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F4-CS2-K3-at0213243140 ; lem-F4-K3-CS2-at0213243140)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-CS14-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R ; lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R ; lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R ; lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS14 ∷ Sw01 ∷ []) (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wl 1455 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ []) (lem-F5-23 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ X4 ∷ []) (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X))
  q13 : Ws → Eqn
  q13 c4 = eqn (Sw23 ∷ Sb0-2-43-1 ∷ []) (Sb0-3-42-1 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) (wl 1456 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Sw34 ∷ Sb0-3-42-1 ∷ []) (Sb0-4-32-1 ∷ Sw34 ∷ []) (lem-comm-push-SBOX⟨0·3·42·1⟩-sw3-R (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (Sw12 ∷ X3 ∷ []) (X3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X))
  q17 : Ws → Eqn
  q17 c4 = eqn (Sw12 ∷ Sb0-4-32-1 ∷ []) (Sb0-4-31-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) (wl 1457 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw23 ∷ Sb0-4-31-2 ∷ []) (Sb0-4-21-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·4·31·2⟩-sw2-R (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (c₂ (Swap) (X))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw01 ∷ Sb0-4-21-3 ∷ []) (Sb1-4-20-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·4·21·3⟩-sw0-R (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) (wl 1458 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw12 ∷ Sb1-4-20-3 ∷ []) (Sb2-4-10-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wl 1459 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw01 ∷ Sb2-4-10-3 ∷ []) (Sb2-4-01-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨2·4·10·3⟩-sw0-R (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (K1 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (wl 1460 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-CS2-at0213243140 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-K3-at0213243140 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-CS2-at0213243140 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-K3-at0213243140 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (S4 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (wp 1306 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-CS2-at0213243140 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-K3-at0213243140 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-S2-at0213243140 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ []) (wl 1461 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-S2-at0213243140 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-CS2-at0213243140 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-K3-at0213243140 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-I-at0213243140 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) (lem-F4-CS2-S2-at0213243140 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-I-at0213243140 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (lem-F4-K3-S2-at0213243140 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-F4-S2-I-at0213243140 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (lem-F4-I-I-at0213243140 c4)

-- deb-CKS-split-b @0213243140: 540 steps
lem-deb-CKS-split-b-at0213243140 : Ws → ⟪ (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ []) ⟫ʷ
lem-deb-CKS-split-b-at0213243140 c4 = derive (CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb2-4-01-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S0 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 7 (q13 c4) ∷
   rw 8 (q12 c4) ∷
   rw 9 (q13 c4) ∷
   rw 10 (q6 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q15 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q15 c4) ∷
   rw 9 (q9 c4) ∷
   rw 4 (q16 c4) ∷
   rw 5 (q17 c4) ∷
   rw 6 (q16 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q3 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q18 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q6 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q20 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q1 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q23 c4) ∷
   rw 5 (q3 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q1 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 12 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw 12 (q8 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   re 13 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 15 (q9 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw 14 (q10 c4) ∷
   rw⁻ 15 (q11 c4) ∷
   rw 14 (q12 c4) ∷
   rw 15 (q13 c4) ∷
   rw 16 (q12 c4) ∷
   rw 17 (q13 c4) ∷
   rw 18 (q6 c4) ∷
   rw 13 (q14 c4) ∷
   rw 14 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw 16 (q15 c4) ∷
   rw 17 (q9 c4) ∷
   rw 12 (q16 c4) ∷
   rw 13 (q17 c4) ∷
   rw 14 (q16 c4) ∷
   rw 15 (q17 c4) ∷
   rw 16 (q3 c4) ∷
   rw 11 (q18 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q18 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q6 c4) ∷
   rw 10 (q20 c4) ∷
   rw 11 (q21 c4) ∷
   rw 12 (q20 c4) ∷
   rw 13 (q21 c4) ∷
   rw 14 (q1 c4) ∷
   rw 9 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 11 (q22 c4) ∷
   rw 12 (q23 c4) ∷
   rw 13 (q3 c4) ∷
   rw 8 (q24 c4) ∷
   rw 9 (q25 c4) ∷
   rw 10 (q24 c4) ∷
   rw 11 (q25 c4) ∷
   rw 12 (q1 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw⁻ 6 (q29 c4) ∷
   rw 12 (q26 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw 16 (q2 c4) ∷
   rw⁻ 18 (q3 c4) ∷
   rw 17 (q4 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw 20 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   re 21 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 23 (q9 c4) ∷
   rw⁻ 23 (q6 c4) ∷
   rw 22 (q10 c4) ∷
   rw⁻ 23 (q11 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q13 c4) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q13 c4) ∷
   rw 26 (q6 c4) ∷
   rw 21 (q14 c4) ∷
   rw 22 (q15 c4) ∷
   rw 23 (q14 c4) ∷
   rw 24 (q15 c4) ∷
   rw 25 (q9 c4) ∷
   rw 20 (q16 c4) ∷
   rw 21 (q17 c4) ∷
   rw 22 (q16 c4) ∷
   rw 23 (q17 c4) ∷
   rw 24 (q3 c4) ∷
   rw 19 (q18 c4) ∷
   rw 20 (q19 c4) ∷
   rw 21 (q18 c4) ∷
   rw 22 (q19 c4) ∷
   rw 23 (q6 c4) ∷
   rw 18 (q20 c4) ∷
   rw 19 (q21 c4) ∷
   rw 20 (q20 c4) ∷
   rw 21 (q21 c4) ∷
   rw 22 (q1 c4) ∷
   rw 17 (q22 c4) ∷
   rw 18 (q23 c4) ∷
   rw 19 (q22 c4) ∷
   rw 20 (q23 c4) ∷
   rw 21 (q3 c4) ∷
   rw 16 (q24 c4) ∷
   rw 17 (q25 c4) ∷
   rw 18 (q24 c4) ∷
   rw 19 (q25 c4) ∷
   rw 20 (q1 c4) ∷
   rw⁻ 15 (q28 c4) ∷
   rw⁻ 14 (q29 c4) ∷
   rw⁻ 13 (q28 c4) ∷
   rw⁻ 12 (q29 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw⁻ 18 (q33 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw⁻ 16 (q33 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 24 (q31 c4) ∷
   rw⁻ 23 (q34 c4) ∷
   rw⁻ 22 (q32 c4) ∷
   rw⁻ 21 (q33 c4) ∷
   rw⁻ 20 (q32 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw 28 (q31 c4) ∷
   rw⁻ 27 (q34 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw⁻ 24 (q33 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw⁻ 22 (q33 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw⁻ 32 (q35 c4) ∷
   rw⁻ 31 (q36 c4) ∷
   rw⁻ 30 (q36 c4) ∷
   rw⁻ 29 (q36 c4) ∷
   rw⁻ 28 (q37 c4) ∷
   rw⁻ 27 (q38 c4) ∷
   rw⁻ 26 (q37 c4) ∷
   rw⁻ 25 (q38 c4) ∷
   rw⁻ 24 (q37 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw 36 (q2 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw 37 (q4 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw 38 (q5 c4) ∷
   rw⁻ 40 (q6 c4) ∷
   rw 39 (q7 c4) ∷
   rw⁻ 41 (q3 c4) ∷
   rw 40 (q8 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   re 41 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 43 (q9 c4) ∷
   rw⁻ 43 (q6 c4) ∷
   rw 42 (q10 c4) ∷
   rw⁻ 43 (q11 c4) ∷
   rw 42 (q12 c4) ∷
   rw 43 (q13 c4) ∷
   rw 44 (q12 c4) ∷
   rw 45 (q13 c4) ∷
   rw 46 (q6 c4) ∷
   rw 41 (q14 c4) ∷
   rw 42 (q15 c4) ∷
   rw 43 (q14 c4) ∷
   rw 44 (q15 c4) ∷
   rw 45 (q9 c4) ∷
   rw 40 (q16 c4) ∷
   rw 41 (q17 c4) ∷
   rw 42 (q16 c4) ∷
   rw 43 (q17 c4) ∷
   rw 44 (q3 c4) ∷
   rw 39 (q18 c4) ∷
   rw 40 (q19 c4) ∷
   rw 41 (q18 c4) ∷
   rw 42 (q19 c4) ∷
   rw 43 (q6 c4) ∷
   rw 38 (q20 c4) ∷
   rw 39 (q21 c4) ∷
   rw 40 (q20 c4) ∷
   rw 41 (q21 c4) ∷
   rw 42 (q1 c4) ∷
   rw 37 (q22 c4) ∷
   rw 38 (q23 c4) ∷
   rw 39 (q22 c4) ∷
   rw 40 (q23 c4) ∷
   rw 41 (q3 c4) ∷
   rw 36 (q24 c4) ∷
   rw 37 (q25 c4) ∷
   rw 38 (q24 c4) ∷
   rw 39 (q25 c4) ∷
   rw 40 (q1 c4) ∷
   rw⁻ 35 (q39 c4) ∷
   rw⁻ 34 (q40 c4) ∷
   rw⁻ 33 (q40 c4) ∷
   rw⁻ 32 (q40 c4) ∷
   rw⁻ 31 (q29 c4) ∷
   rw⁻ 30 (q28 c4) ∷
   rw⁻ 29 (q29 c4) ∷
   rw⁻ 28 (q28 c4) ∷
   rw⁻ 27 (q29 c4) ∷
   rw⁻ 41 (q1 c4) ∷
   rw 40 (q2 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw 41 (q4 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw 42 (q5 c4) ∷
   rw⁻ 44 (q6 c4) ∷
   rw 43 (q7 c4) ∷
   rw⁻ 45 (q3 c4) ∷
   rw 44 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   re 45 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 47 (q9 c4) ∷
   rw⁻ 47 (q6 c4) ∷
   rw 46 (q10 c4) ∷
   rw⁻ 47 (q11 c4) ∷
   rw 46 (q12 c4) ∷
   rw 47 (q13 c4) ∷
   rw 48 (q12 c4) ∷
   rw 49 (q13 c4) ∷
   rw 50 (q6 c4) ∷
   rw 45 (q14 c4) ∷
   rw 46 (q15 c4) ∷
   rw 47 (q14 c4) ∷
   rw 48 (q15 c4) ∷
   rw 49 (q9 c4) ∷
   rw 44 (q16 c4) ∷
   rw 45 (q17 c4) ∷
   rw 46 (q16 c4) ∷
   rw 47 (q17 c4) ∷
   rw 48 (q3 c4) ∷
   rw 43 (q18 c4) ∷
   rw 44 (q19 c4) ∷
   rw 45 (q18 c4) ∷
   rw 46 (q19 c4) ∷
   rw 47 (q6 c4) ∷
   rw 42 (q20 c4) ∷
   rw 43 (q21 c4) ∷
   rw 44 (q20 c4) ∷
   rw 45 (q21 c4) ∷
   rw 46 (q1 c4) ∷
   rw 41 (q22 c4) ∷
   rw 42 (q23 c4) ∷
   rw 43 (q22 c4) ∷
   rw 44 (q23 c4) ∷
   rw 45 (q3 c4) ∷
   rw 40 (q24 c4) ∷
   rw 41 (q25 c4) ∷
   rw 42 (q24 c4) ∷
   rw 43 (q25 c4) ∷
   rw 44 (q1 c4) ∷
   rw⁻ 39 (q29 c4) ∷
   rw⁻ 38 (q39 c4) ∷
   rw⁻ 37 (q40 c4) ∷
   rw⁻ 36 (q40 c4) ∷
   rw⁻ 35 (q40 c4) ∷
   rw⁻ 34 (q29 c4) ∷
   rw⁻ 33 (q28 c4) ∷
   rw⁻ 32 (q29 c4) ∷
   rw⁻ 31 (q28 c4) ∷
   rw⁻ 30 (q29 c4) ∷
   rw 44 (q26 c4) ∷
   rw⁻ 43 (q27 c4) ∷
   rw⁻ 42 (q27 c4) ∷
   rw⁻ 41 (q41 c4) ∷
   rw⁻ 40 (q42 c4) ∷
   rw⁻ 39 (q42 c4) ∷
   rw⁻ 38 (q42 c4) ∷
   rw⁻ 37 (q27 c4) ∷
   rw⁻ 36 (q30 c4) ∷
   rw⁻ 35 (q27 c4) ∷
   rw⁻ 34 (q30 c4) ∷
   rw⁻ 33 (q27 c4) ∷
   rw⁻ 49 (q1 c4) ∷
   rw 48 (q2 c4) ∷
   rw⁻ 50 (q3 c4) ∷
   rw 49 (q4 c4) ∷
   rw⁻ 51 (q1 c4) ∷
   rw 50 (q5 c4) ∷
   rw⁻ 52 (q6 c4) ∷
   rw 51 (q7 c4) ∷
   rw⁻ 53 (q3 c4) ∷
   rw 52 (q8 c4) ∷
   rw⁻ 54 (q9 c4) ∷
   re 53 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 55 (q9 c4) ∷
   rw⁻ 55 (q6 c4) ∷
   rw 54 (q10 c4) ∷
   rw⁻ 55 (q11 c4) ∷
   rw 54 (q12 c4) ∷
   rw 55 (q13 c4) ∷
   rw 56 (q12 c4) ∷
   rw 57 (q13 c4) ∷
   rw 58 (q6 c4) ∷
   rw 53 (q14 c4) ∷
   rw 54 (q15 c4) ∷
   rw 55 (q14 c4) ∷
   rw 56 (q15 c4) ∷
   rw 57 (q9 c4) ∷
   rw 52 (q16 c4) ∷
   rw 53 (q17 c4) ∷
   rw 54 (q16 c4) ∷
   rw 55 (q17 c4) ∷
   rw 56 (q3 c4) ∷
   rw 51 (q18 c4) ∷
   rw 52 (q19 c4) ∷
   rw 53 (q18 c4) ∷
   rw 54 (q19 c4) ∷
   rw 55 (q6 c4) ∷
   rw 50 (q20 c4) ∷
   rw 51 (q21 c4) ∷
   rw 52 (q20 c4) ∷
   rw 53 (q21 c4) ∷
   rw 54 (q1 c4) ∷
   rw 49 (q22 c4) ∷
   rw 50 (q23 c4) ∷
   rw 51 (q22 c4) ∷
   rw 52 (q23 c4) ∷
   rw 53 (q3 c4) ∷
   rw 48 (q24 c4) ∷
   rw 49 (q25 c4) ∷
   rw 50 (q24 c4) ∷
   rw 51 (q25 c4) ∷
   rw 52 (q1 c4) ∷
   rw⁻ 47 (q28 c4) ∷
   rw⁻ 46 (q29 c4) ∷
   rw⁻ 45 (q29 c4) ∷
   rw⁻ 44 (q39 c4) ∷
   rw⁻ 43 (q40 c4) ∷
   rw⁻ 42 (q40 c4) ∷
   rw⁻ 41 (q40 c4) ∷
   rw⁻ 40 (q29 c4) ∷
   rw⁻ 39 (q28 c4) ∷
   rw⁻ 38 (q29 c4) ∷
   rw⁻ 37 (q28 c4) ∷
   rw⁻ 36 (q29 c4) ∷
   rw 52 (q26 c4) ∷
   rw⁻ 51 (q27 c4) ∷
   rw⁻ 50 (q30 c4) ∷
   rw⁻ 49 (q27 c4) ∷
   rw⁻ 48 (q27 c4) ∷
   rw⁻ 47 (q41 c4) ∷
   rw⁻ 46 (q42 c4) ∷
   rw⁻ 45 (q42 c4) ∷
   rw⁻ 44 (q42 c4) ∷
   rw⁻ 43 (q27 c4) ∷
   rw⁻ 42 (q30 c4) ∷
   rw⁻ 41 (q27 c4) ∷
   rw⁻ 40 (q30 c4) ∷
   rw⁻ 39 (q27 c4) ∷
   rw⁻ 57 (q1 c4) ∷
   rw 56 (q2 c4) ∷
   rw⁻ 58 (q3 c4) ∷
   rw 57 (q4 c4) ∷
   rw⁻ 59 (q1 c4) ∷
   rw 58 (q5 c4) ∷
   rw⁻ 60 (q6 c4) ∷
   rw 59 (q7 c4) ∷
   rw⁻ 61 (q3 c4) ∷
   rw 60 (q8 c4) ∷
   rw⁻ 62 (q9 c4) ∷
   re 61 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 63 (q9 c4) ∷
   rw⁻ 63 (q6 c4) ∷
   rw 62 (q10 c4) ∷
   rw⁻ 63 (q11 c4) ∷
   rw 62 (q12 c4) ∷
   rw 63 (q13 c4) ∷
   rw 64 (q12 c4) ∷
   rw 65 (q13 c4) ∷
   rw 66 (q6 c4) ∷
   rw 61 (q14 c4) ∷
   rw 62 (q15 c4) ∷
   rw 63 (q14 c4) ∷
   rw 64 (q15 c4) ∷
   rw 65 (q9 c4) ∷
   rw 60 (q16 c4) ∷
   rw 61 (q17 c4) ∷
   rw 62 (q16 c4) ∷
   rw 63 (q17 c4) ∷
   rw 64 (q3 c4) ∷
   rw 59 (q18 c4) ∷
   rw 60 (q19 c4) ∷
   rw 61 (q18 c4) ∷
   rw 62 (q19 c4) ∷
   rw 63 (q6 c4) ∷
   rw 58 (q20 c4) ∷
   rw 59 (q21 c4) ∷
   rw 60 (q20 c4) ∷
   rw 61 (q21 c4) ∷
   rw 62 (q1 c4) ∷
   rw 57 (q22 c4) ∷
   rw 58 (q23 c4) ∷
   rw 59 (q22 c4) ∷
   rw 60 (q23 c4) ∷
   rw 61 (q3 c4) ∷
   rw 56 (q24 c4) ∷
   rw 57 (q25 c4) ∷
   rw 58 (q24 c4) ∷
   rw 59 (q25 c4) ∷
   rw 60 (q1 c4) ∷
   rw⁻ 55 (q28 c4) ∷
   rw⁻ 54 (q29 c4) ∷
   rw⁻ 53 (q28 c4) ∷
   rw⁻ 52 (q29 c4) ∷
   rw⁻ 51 (q29 c4) ∷
   rw⁻ 50 (q39 c4) ∷
   rw⁻ 49 (q40 c4) ∷
   rw⁻ 48 (q40 c4) ∷
   rw⁻ 47 (q40 c4) ∷
   rw⁻ 46 (q29 c4) ∷
   rw⁻ 45 (q28 c4) ∷
   rw⁻ 44 (q29 c4) ∷
   rw⁻ 43 (q28 c4) ∷
   rw⁻ 42 (q29 c4) ∷
   rw 60 (q31 c4) ∷
   rw⁻ 59 (q32 c4) ∷
   rw⁻ 58 (q33 c4) ∷
   rw⁻ 57 (q32 c4) ∷
   rw⁻ 56 (q33 c4) ∷
   rw⁻ 55 (q32 c4) ∷
   rw⁻ 54 (q32 c4) ∷
   rw⁻ 53 (q43 c4) ∷
   rw⁻ 52 (q34 c4) ∷
   rw⁻ 51 (q34 c4) ∷
   rw⁻ 50 (q34 c4) ∷
   rw⁻ 49 (q32 c4) ∷
   rw⁻ 48 (q33 c4) ∷
   rw⁻ 47 (q32 c4) ∷
   rw⁻ 46 (q33 c4) ∷
   rw⁻ 45 (q32 c4) ∷
   rw 64 (q31 c4) ∷
   rw⁻ 63 (q34 c4) ∷
   rw⁻ 62 (q32 c4) ∷
   rw⁻ 61 (q33 c4) ∷
   rw⁻ 60 (q32 c4) ∷
   rw⁻ 59 (q33 c4) ∷
   rw⁻ 58 (q32 c4) ∷
   rw⁻ 57 (q32 c4) ∷
   rw⁻ 56 (q43 c4) ∷
   rw⁻ 55 (q34 c4) ∷
   rw⁻ 54 (q34 c4) ∷
   rw⁻ 53 (q34 c4) ∷
   rw⁻ 52 (q32 c4) ∷
   rw⁻ 51 (q33 c4) ∷
   rw⁻ 50 (q32 c4) ∷
   rw⁻ 49 (q33 c4) ∷
   rw⁻ 48 (q32 c4) ∷
   rw 68 (q31 c4) ∷
   rw⁻ 67 (q34 c4) ∷
   rw⁻ 66 (q34 c4) ∷
   rw⁻ 65 (q32 c4) ∷
   rw⁻ 64 (q33 c4) ∷
   rw⁻ 63 (q32 c4) ∷
   rw⁻ 62 (q33 c4) ∷
   rw⁻ 61 (q32 c4) ∷
   rw⁻ 60 (q32 c4) ∷
   rw⁻ 59 (q43 c4) ∷
   rw⁻ 58 (q34 c4) ∷
   rw⁻ 57 (q34 c4) ∷
   rw⁻ 56 (q34 c4) ∷
   rw⁻ 55 (q32 c4) ∷
   rw⁻ 54 (q33 c4) ∷
   rw⁻ 53 (q32 c4) ∷
   rw⁻ 52 (q33 c4) ∷
   rw⁻ 51 (q32 c4) ∷
   rw⁻ 72 (q35 c4) ∷
   rw⁻ 71 (q36 c4) ∷
   rw⁻ 70 (q36 c4) ∷
   rw⁻ 69 (q36 c4) ∷
   rw⁻ 68 (q37 c4) ∷
   rw⁻ 67 (q38 c4) ∷
   rw⁻ 66 (q37 c4) ∷
   rw⁻ 65 (q38 c4) ∷
   rw⁻ 64 (q37 c4) ∷
   rw⁻ 63 (q37 c4) ∷
   rw⁻ 62 (q44 c4) ∷
   rw⁻ 61 (q36 c4) ∷
   rw⁻ 60 (q36 c4) ∷
   rw⁻ 59 (q36 c4) ∷
   rw⁻ 58 (q37 c4) ∷
   rw⁻ 57 (q38 c4) ∷
   rw⁻ 56 (q37 c4) ∷
   rw⁻ 55 (q38 c4) ∷
   rw⁻ 54 (q37 c4) ∷ []) Eq.refl
