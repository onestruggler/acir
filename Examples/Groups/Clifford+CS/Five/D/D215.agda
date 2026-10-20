{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D215 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-1b52048e)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box2-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-CKc-box-at0312203441 ; lem-F1-comm-CS-S1at2 ; lem-S2-SBOX⟨3·0·41·2⟩ ; lem-S2-SBOX⟨3·1·42·0⟩ ; lem-box-perm-3421-at03243240 ; lem-box-perm-4312-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.D029 using (lem-L-CCZ-0-part2)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D043 using (lem-L-CCZ-0-part1 ; lem-L-CCZ-0-part3)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-X-CS1at2 ; lem-F1-comm-CSu-CSat1)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-F0-at01143043 ; lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D195 using (lem-deb-Q-hi)
open import Examples.Groups.Clifford+CS.Five.D.D198 using (lem-deb-Q-lo-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D205 using (lem-nf-rel-268at0)
open import Examples.Groups.Clifford+CS.Five.D.D206 using (lem-L-CCZ-0-part0 ; lem-deb-P-hi ; lem-deb-P-hi-at02132031 ; lem-deb-P-hi-at132132 ; lem-deb-P-lo-at02132031 ; lem-deb-P-lo-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D207 using (lem-deb-rel-272at1-R)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ134-CX02)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx3-1420 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (Toff302 ∷ Toff024 ∷ []) (wp 1025 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (Toff024 ∷ []) (wp 1026 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (K0 ∷ CCZ134 ∷ []) (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) (wl 1220 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ []) (wl 1221 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp 1003 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (K0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl 1206 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Toff302 ∷ Toff324 ∷ []) (Toff324 ∷ Toff302 ∷ []) (wp 1007 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp 1006 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Toff302 ∷ CX14 ∷ []) (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ []) (wp 1005 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl 1190 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff024 ∷ Toff324 ∷ Toff324 ∷ []) (Toff024 ∷ []) (wp 1008 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) (wl 1222 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS01 ∷ Toff302 ∷ []) (Toff302 ∷ CS01 ∷ []) (wl 1223 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) (wp 261 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS01⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS01⁻ ∷ []) (wl 1224 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ134 ∷ []) (wp 1027 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx3-1420 ∷ []) (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx3-2041 ∷ CK41 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx3-2041 ∷ []) (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp 301 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff302 ∷ CS14 ∷ []) (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CX01 ∷ Toff302 ∷ []) (Toff302 ∷ CX01 ∷ []) (wl 1233 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Toff302 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS04 ∷ Toff302 ∷ []) (Toff302 ∷ CS04 ∷ []) (wp 1041 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp 272 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (S4 ∷ Toff302 ∷ []) (Toff302 ∷ S4 ∷ []) (wp 1111 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ134 ∷ S4 ∷ []) (S4 ∷ CCZ134 ∷ []) (wl 1249 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ012 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ012 ∷ []) (wl 1251 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl 391 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ134 ∷ CS12 ∷ []) (CS12 ∷ CCZ134 ∷ []) (wl 393 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ134 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ134 ∷ []) (wl 392 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx3-1420 ∷ Bx3-1420 ∷ []) [] (lem-box2-at03243240 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ124 ∷ CS01 ∷ Toff024 ∷ []) (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp 1042 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ []) (CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ []) (wp 1123 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl 341 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) (wp 167 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ []) (S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ []) (wp 1124 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) (wp 743 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (wp 1125 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (lem-nf-rel-268at0 c4)

-- F1-rel-268@0: 484 steps
lem-F1-rel-268at0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268at0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 3 (q2 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 10 (q2 c4) ∷
   rw 11 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 5 (q4 c4) ∷
   rw 8 (q3 c4) ∷
   re 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 2 1 (CS01 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
   re 10 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 12 1 (CS01 ∷ []) ∷
   re 14 1 (CS01⁻ ∷ []) ∷
   rw 10 (q5 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 13 (q15 c4) ∷
   rw 15 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q18 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw 17 (q18 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw 11 (q21 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw 14 (q24 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q12 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 14 (q6 c4) ∷
   rw 16 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 13 (q8 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q12 c4) ∷
   rw⁻ 19 (q13 c4) ∷
   rw 13 (q7 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw 17 (q26 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw 15 (q26 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 16 (q27 c4) ∷
   rw 16 (q28 c4) ∷
   rw 19 (q29 c4) ∷
   rw 19 (q5 c4) ∷
   rw 23 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw 24 (q33 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 22 (q30 c4) ∷
   rw⁻ 21 (q35 c4) ∷
   rw 21 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw 22 (q33 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw⁻ 24 (q34 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw⁻ 19 (q35 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw 20 (q27 c4) ∷
   rw 20 (q28 c4) ∷
   rw 23 (q29 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q36 c4) ∷
   rw 25 (q37 c4) ∷
   rw⁻ 24 (q36 c4) ∷
   rw 23 (q37 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 3 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 0 (q7 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 6 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 5 (q10 c4) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 5 (q26 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 6 (q27 c4) ∷
   rw 6 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 9 (q5 c4) ∷
   rw 13 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw 14 (q33 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw⁻ 16 (q34 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw⁻ 11 (q35 c4) ∷
   rw 11 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 11 (q32 c4) ∷
   rw 12 (q33 c4) ∷
   rw⁻ 13 (q32 c4) ∷
   rw⁻ 14 (q34 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw⁻ 9 (q35 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw 10 (q27 c4) ∷
   rw 10 (q28 c4) ∷
   rw 13 (q29 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 16 (q36 c4) ∷
   rw 15 (q37 c4) ∷
   rw⁻ 14 (q36 c4) ∷
   rw 13 (q37 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw 14 (q5 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw 16 (q16 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw 16 (q18 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q12 c4) ∷
   rw⁻ 23 (q13 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q14 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   rw 18 (q15 c4) ∷
   rw 20 (q16 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw 22 (q18 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 16 (q21 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q12 c4) ∷
   rw⁻ 21 (q13 c4) ∷
   rw 15 (q7 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q20 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 19 (q22 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 17 (q22 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw 20 (q24 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw 18 (q24 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q10 c4) ∷
   rw 26 (q12 c4) ∷
   rw⁻ 27 (q13 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q14 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 22 (q15 c4) ∷
   rw 24 (q16 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw 24 (q18 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw 26 (q18 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw 20 (q21 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q12 c4) ∷
   rw⁻ 25 (q13 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 20 (q22 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 28 (q20 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 21 (q22 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw 24 (q26 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw 22 (q26 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q38 c4) ∷
   rw 26 (q39 c4) ∷
   rw 25 (q40 c4) ∷
   rw 26 (q10 c4) ∷
   rw 27 (q41 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q24 c4) ∷
   rw⁻ 25 (q39 c4) ∷
   rw⁻ 24 (q38 c4) ∷
   rw 24 (q39 c4) ∷
   rw 23 (q40 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q41 c4) ∷
   rw 26 (q10 c4) ∷
   rw 27 (q24 c4) ∷
   rw⁻ 23 (q39 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 24 (q27 c4) ∷
   rw 24 (q28 c4) ∷
   rw 27 (q29 c4) ∷
   rw 27 (q5 c4) ∷
   rw⁻ 30 (q38 c4) ∷
   rw 30 (q39 c4) ∷
   rw 29 (q40 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q41 c4) ∷
   rw 32 (q10 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 29 (q39 c4) ∷
   rw⁻ 28 (q38 c4) ∷
   rw 28 (q39 c4) ∷
   rw 27 (q40 c4) ∷
   rw 28 (q10 c4) ∷
   rw 29 (q41 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q24 c4) ∷
   rw⁻ 27 (q39 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 28 (q5 c4) ∷
   rw 32 (q30 c4) ∷
   rw 31 (q31 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw 33 (q33 c4) ∷
   rw⁻ 34 (q32 c4) ∷
   rw⁻ 35 (q34 c4) ∷
   rw⁻ 31 (q30 c4) ∷
   rw⁻ 30 (q35 c4) ∷
   rw 30 (q30 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 30 (q32 c4) ∷
   rw 31 (q33 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw⁻ 33 (q34 c4) ∷
   rw⁻ 29 (q30 c4) ∷
   rw⁻ 28 (q35 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 32 (q38 c4) ∷
   rw 32 (q39 c4) ∷
   rw 31 (q40 c4) ∷
   rw 32 (q10 c4) ∷
   rw 33 (q41 c4) ∷
   rw 34 (q10 c4) ∷
   rw 35 (q24 c4) ∷
   rw⁻ 31 (q39 c4) ∷
   rw⁻ 30 (q38 c4) ∷
   rw 30 (q39 c4) ∷
   rw 29 (q40 c4) ∷
   rw 30 (q10 c4) ∷
   rw 31 (q41 c4) ∷
   rw 32 (q10 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 29 (q39 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 30 (q27 c4) ∷
   rw 30 (q28 c4) ∷
   rw 33 (q29 c4) ∷
   rw 33 (q5 c4) ∷
   rw⁻ 36 (q38 c4) ∷
   rw 36 (q39 c4) ∷
   rw 35 (q40 c4) ∷
   rw 36 (q10 c4) ∷
   rw 37 (q41 c4) ∷
   rw 38 (q10 c4) ∷
   rw 39 (q24 c4) ∷
   rw⁻ 35 (q39 c4) ∷
   rw⁻ 34 (q38 c4) ∷
   rw 34 (q39 c4) ∷
   rw 33 (q40 c4) ∷
   rw 34 (q10 c4) ∷
   rw 35 (q41 c4) ∷
   rw 36 (q10 c4) ∷
   rw 37 (q24 c4) ∷
   rw⁻ 33 (q39 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw⁻ 37 (q36 c4) ∷
   rw 36 (q37 c4) ∷
   rw⁻ 35 (q36 c4) ∷
   rw 34 (q37 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw 35 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 29 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw 6 (q46 c4) ∷
   rw 7 (q48 c4) ∷
   rw 17 (q46 c4) ∷
   rw 8 (q49 c4) ∷
   rw 9 (q44 c4) ∷
   rw 9 (q43 c4) ∷
   rw 11 (q44 c4) ∷
   rw 15 (q46 c4) ∷
   rw 16 (q46 c4) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (lem-L-CCZ-0-part0 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) (lem-L-CCZ-0-part1 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ []) (lem-L-CCZ-0-part2 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ []) (Bx3-0124 ∷ []) (lem-L-CCZ-0-part3 c4)

-- L-CCZ-0: 4 steps
lem-L-CCZ-0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-L-CCZ-0 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 0 (q54 c4) ∷
   rw 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (lem-deb-P-hi-at02132031 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) (wp 1264 c4)

-- F1-CS-K0@0: 3 steps
lem-F1-CS-K0at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K0at0 c4 = derive (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q56 c4) ∷
   rw 0 (q57 c4) ∷
   rw⁻ 2 (q56 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-P-hi-at132132 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)
  q60 : Ws → Eqn
  q60 c4 = eqn (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (wp 1266 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)

-- F1-CS-K0@1: 7 steps
lem-F1-CS-K0at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K0at1 c4 = derive (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q58 c4) ∷
   rw 16 (q59 c4) ∷
   rw 35 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 18 (q61 c4) ∷
   rw 37 (q61 c4) ∷
   rw⁻ 2 (q58 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-P-lo-at02132031 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (wp 1268 c4)

-- F1-CS-K1@0: 3 steps
lem-F1-CS-K1at0 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-CS-K1at0 c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  (rw 0 (q62 c4) ∷
   rw 0 (q63 c4) ∷
   rw⁻ 2 (q62 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-deb-P-lo-at132132 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (wp 1269 c4)

-- F1-CS-K1@1: 7 steps
lem-F1-CS-K1at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K1at1 c4 = derive (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  (rw 0 (q64 c4) ∷
   rw 16 (q59 c4) ∷
   rw 35 (q59 c4) ∷
   rw 0 (q65 c4) ∷
   rw 18 (q61 c4) ∷
   rw 37 (q61 c4) ∷
   rw⁻ 2 (q64 c4) ∷ []) Eq.refl

-- deb-rel-269@0-R: 2 steps
lem-deb-rel-269at0-R : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-rel-269at0-R c4 = derive (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 0 (q62 c4) ∷
   rw 42 (q58 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-deb-P-hi c4)

-- deb-rel-269@1-R: 2 steps
lem-deb-rel-269at1-R : Ws → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-rel-269at1-R c4 = derive (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  (rw 0 (q64 c4) ∷
   rw 42 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn [] (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-TR2-1b52048e c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-deb-Q-hi c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-deb-Q-lo-at132132 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) (lem-F1-comm-CSu-CSat1 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (wp 1273 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) (lem-deb-rel-272at1-R c4)

-- F1-rel-272@1: 26 steps
lem-F1-rel-272at1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-272at1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 8 (q67 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw 10 (q69 c4) ∷
   rw 9 (q70 c4) ∷
   rw 10 (q70 c4) ∷
   rw 11 (q70 c4) ∷
   rw 12 (q70 c4) ∷
   rw 13 (q68 c4) ∷
   rw 8 (q71 c4) ∷
   rw 9 (q71 c4) ∷
   rw 10 (q71 c4) ∷
   rw 11 (q71 c4) ∷
   rw 12 (q67 c4) ∷
   rw 0 (q72 c4) ∷
   rw 33 (q73 c4) ∷
   rw⁻ 65 (q74 c4) ∷
   rw 9 (q59 c4) ∷
   rw 28 (q59 c4) ∷
   rw 42 (q59 c4) ∷
   rw 61 (q59 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 9 (q61 c4) ∷
   rw 28 (q61 c4) ∷
   rw 42 (q61 c4) ∷
   rw 61 (q61 c4) ∷
   rw⁻ 0 (q76 c4) ∷ []) Eq.refl
