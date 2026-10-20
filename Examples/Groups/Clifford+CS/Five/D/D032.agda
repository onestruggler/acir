{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D032 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0263 ; wl1380 ; wp0066 ; wp0161 ; wl0214 ; wl0220 ; wl0221 ; wl0222 ; wp0053 ; wp0061 ; wp0065 ; wp0069 ; wp0070 ; wl0187 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0323 ; wl1182 ; wp0021 ; wp0032 ; wp0033 ; wp0034 ; wp0036 ; wp0037 ; wp0039 ; wp0041 ; wp0042 ; wp0044 ; wp0179 ; wp0651 ; wp0746 ; wp0905 ; wl0188 ; wl0189 ; wl0198 ; wl1411 ; wp0029 ; wp0030 ; wp0031 ; wp0038 ; wp1259 ; wp1260 ; wp1261 ; wp1262 ; wp1263 ; wl0211 ; wl0219 ; wl0314 ; wl1000 ; wl1113 ; wl1413 ; wp0060 ; wp0062 ; wp0064 ; wp0067 ; wp0068 ; wp0071 ; wp0072 ; wp0074 ; wp0265 ; wp0722 ; wl0212 ; wl0213 ; wl0215 ; wl0216 ; wl1414 ; wl1415 ; wl1416 ; wp0073 ; wp1265 ; wl1420 ; wp1267 ; wp1274 ; wl0807 ; wl0808 ; wl0921 ; wl1421 ; wl1422 ; wp0035 ; wp0760 ; wp1143 ; wp1275 ; wp1276 ; wp1277 ; wl1439 ; wl1441 ; wl1442 ; wl1443 ; wp1292 ; wp1294)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-I ; lem-F4-I-K0 ; lem-F4-I-S0 ; lem-F4-K0-I ; lem-F4-K0-K0 ; lem-F4-K0-S0 ; lem-F4-S0-I ; lem-F4-S0-K0 ; lem-F4-S0-S0 ; lem-sym-ab-at03102132 ; lem-sym-ab-at032032 ; lem-sym-ab-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at03122130 ; lem-sym-ab-at0330 ; lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab-at0310213442 ; lem-sym-ab-at0314213042 ; lem-sym-ab-at03203442 ; lem-sym-ab-at03243042 ; lem-sym-ab-at142142 ; lem-sym-ab-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-sym-bc-at03102132 ; lem-sym-bc-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-box-cP-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at0214203143 ; lem-box-cP-at243243 ; lem-sym-bc-at0310243142 ; lem-sym-bc-at031031 ; lem-sym-bc-at132132 ; lem-sym-bc-at1331 ; lem-sym-bc-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-I-CS0 ; lem-F4-K0-CS0 ; lem-F4-S0-CS0 ; lem-Xb-box-at0210243143 ; lem-Xb-box-at243243 ; lem-box2-at0210243143 ; lem-box2-at243243 ; lem-pairs-at0310243142 ; lem-pairs-at0330 ; lem-pairs-at1331 ; lem-pairs-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-pairs-at031031 ; lem-pairs-at03243042 ; lem-pairs-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-box2-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-box-perm-1423-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX04-TOFF213 ; lem-comm-CX14-TOFF023 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX40-TOFF213)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx3-2104 ∷ []) (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx3-1204 ∷ []) (Bx3-0412 ∷ []) (lem-pairs-at0330 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx3-0142 ∷ []) (Bx3-1042 ∷ []) (lem-sym-ab-at0310213442 c4)

-- box-perm-2341 @03122130: 4 steps
lem-box-perm-2341-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-box-perm-2341-at03122130 c4 = derive (Bx3-2104 ∷ []) (Bx3-1042 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx3-1042 ∷ []) (Bx3-0142 ∷ []) (lem-sym-ab-at03203442 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (Bx3-0412 ∷ []) (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Bx3-1204 ∷ []) (Bx3-2104 ∷ []) (lem-sym-ab-at0330 c4)

-- box-perm-4123 @03203442: 4 steps
lem-box-perm-4123-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-box-perm-4123-at03203442 c4 = derive (Bx3-1042 ∷ []) (Bx3-2104 ∷ [])
  (rw 0 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 0 (q7 c4) ∷
   rw 0 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (Bx3-1024 ∷ []) (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0214 ∷ []) (lem-sym-bc-at03102132 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx3-0214 ∷ []) (Bx3-1402 ∷ []) (lem-pairs-at031031 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx3-1402 ∷ []) (Bx3-4102 ∷ []) (lem-sym-ab-at03243042 c4)

-- box-perm-4123 @032032: 4 steps
lem-box-perm-4123-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-box-perm-4123-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-4102 ∷ [])
  (rw 0 (q9 c4) ∷
   rw 0 (q10 c4) ∷
   rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx0-1423 ∷ []) (Bx0-1243 ∷ []) (lem-sym-bc-at243243 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Bx0-1243 ∷ []) (Bx0-4312 ∷ []) (lem-pairs-at3443 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Bx0-4312 ∷ []) (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4)

-- box-perm-4123 @14213243: 4 steps
lem-box-perm-4123-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-4123-at14213243 c4 = derive (Bx0-4123 ∷ []) (Bx0-3412 ∷ [])
  (rw 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx3-4102 ∷ []) (Bx3-1402 ∷ []) (lem-sym-ab-at0314213042 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx3-1402 ∷ []) (Bx3-0214 ∷ []) (lem-pairs-at03243042 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx3-0214 ∷ []) (Bx3-0124 ∷ []) (lem-sym-bc-at031031 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx3-0124 ∷ []) (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4)

-- box-perm-2341 @0314213042: 4 steps
lem-box-perm-2341-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2341-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-1024 ∷ [])
  (rw 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 0 (q19 c4) ∷
   rw 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx0-4132 ∷ []) (Bx0-1432 ∷ []) (lem-sym-ab-at142142 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx0-1432 ∷ []) (Bx0-3214 ∷ []) (lem-pairs-at2442 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx0-3214 ∷ []) (Bx0-3124 ∷ []) (lem-sym-bc-at1331 c4)

-- box-perm-3241 @142142: 3 steps
lem-box-perm-3241-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-3241-at142142 c4 = derive (Bx0-4132 ∷ []) (Bx0-3124 ∷ [])
  (rw 0 (q21 c4) ∷
   rw 0 (q22 c4) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx0-3124 ∷ []) (Bx0-3214 ∷ []) (lem-sym-bc-at132132 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx0-3214 ∷ []) (Bx0-1432 ∷ []) (lem-pairs-at1331 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Bx0-1432 ∷ []) (Bx0-4132 ∷ []) (lem-sym-ab-at2442 c4)

-- box-perm-4213 @132132: 3 steps
lem-box-perm-4213-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-4213-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-4132 ∷ [])
  (rw 0 (q24 c4) ∷
   rw 0 (q25 c4) ∷
   rw 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl1182 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp0036 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ []) (wp0746 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp0034 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp0037 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff213 ∷ []) (wl0192 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ024 ∷ []) (wp0042 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CX04 ∷ Toff213 ∷ []) (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (wp0044 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp0021 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx2-0413 ∷ Bx2-0413 ∷ []) [] (lem-box2-at0210243143 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0161 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0905 c4)

-- S2-SBOX(0;2;43;1) @02132031: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at02132031 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at02132031 c4 = derive (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 4 (q30 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 12 (q31 c4) ∷
   rw⁻ 11 (q32 c4) ∷
   rw 10 (q33 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 7 (q30 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw 7 (q39 c4) ∷
   rw 11 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 9 (q42 c4) ∷
   rw 8 (q41 c4) ∷
   rw 7 (q43 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw⁻ 6 (q44 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 2 (q27 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw 2 (q30 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q30 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 5 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 8 (q41 c4) ∷
   rw 7 (q42 c4) ∷
   rw 6 (q41 c4) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 0 (q48 c4) ∷
   rw 0 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Sb⁻2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Sb⁻2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (X))
  q53 : Ws → Eqn
  q53 c4 = eqn (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl0187 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (Sb2-0-3-1 ∷ X4 ∷ []) (X4 ∷ Sb2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (X))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS03 ∷ CX13 ∷ []) (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) (wl0188 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CX13 ∷ Toff314 ∷ []) (Toff314 ∷ CX13 ∷ []) (wl0189 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS01 ∷ Toff314 ∷ []) (Toff314 ∷ CS01 ∷ []) (wp0029 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ []) (wp0030 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (X4 ∷ CX13 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0031 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (X4 ∷ Bx2-0413 ∷ X4 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ []) (lem-Xb-box-at0210243143 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ024 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ024 ∷ []) (wp0179 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp0039 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) (wp1259 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ014 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ []) (wp1260 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CS01 ∷ CCZ014 ∷ []) (CS01 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (wp1261 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Toff214 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ []) (wl0198 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CS01 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp1262 c4)

-- F5-23 @02132031: 112 steps
lem-F5-23-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-23-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 5 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   re 4 1 (CS03 ∷ []) ∷
   rw 4 (q55 c4) ∷
   re 7 1 (Sb2-0-3-1 ∷ []) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 9 (q27 c4) ∷
   re 8 1 (CS03⁻ ∷ []) ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 13 (q31 c4) ∷
   rw⁻ 12 (q32 c4) ∷
   rw 11 (q33 c4) ∷
   rw⁻ 10 (q34 c4) ∷
   rw 9 (q33 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw 8 (q30 c4) ∷
   re 6 1 (CS03 ∷ []) ∷
   rw⁻ 6 (q46 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 10 (q32 c4) ∷
   rw 9 (q33 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   rw 6 (q30 c4) ∷
   rw 4 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q63 c4) ∷
   rw 2 (q33 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 2 (q65 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 5 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 8 (q41 c4) ∷
   rw 7 (q42 c4) ∷
   rw 6 (q41 c4) ∷
   rw 5 (q43 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 15 (q31 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw 13 (q33 c4) ∷
   rw⁻ 12 (q34 c4) ∷
   rw 11 (q33 c4) ∷
   rw⁻ 10 (q35 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   rw 10 (q30 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw 7 (q61 c4) ∷
   rw⁻ 6 (q64 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q30 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 5 (q66 c4) ∷
   rw 11 (q29 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw 9 (q39 c4) ∷
   rw 13 (q40 c4) ∷
   rw 12 (q41 c4) ∷
   rw 11 (q42 c4) ∷
   rw 10 (q41 c4) ∷
   rw 9 (q43 c4) ∷
   rw⁻ 10 (q39 c4) ∷
   rw⁻ 8 (q44 c4) ∷
   rw 7 (q40 c4) ∷
   rw 6 (q47 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw⁻ 9 (q67 c4) ∷
   rw 5 (q68 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 0 (q48 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl1413 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp0064 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CX32 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ014 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ014 ∷ []) (wp0722 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp0062 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) (wp0065 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ Toff023 ∷ []) (wp0068 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ014 ∷ []) (wp0071 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) (wp0070 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) (wp0072 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (wp0074 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp0053 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (Bx0-1423 ∷ Bx0-1423 ∷ []) [] (lem-box2-at243243 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0263 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ124 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl1113 (lit c4))

-- S2-SBOX(0;2;43;1) @132132: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at132132 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at132132 c4 = derive (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   re 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 2 1 (CS13 ∷ []) ∷
   re 4 1 (CS13⁻ ∷ []) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 7 (q72 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   rw 4 (q70 c4) ∷
   rw⁻ 3 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw⁻ 8 (q75 c4) ∷
   rw 7 (q76 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw 5 (q76 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 3 (q79 c4) ∷
   rw 4 (q73 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   rw⁻ 12 (q74 c4) ∷
   rw⁻ 11 (q75 c4) ∷
   rw 10 (q76 c4) ∷
   rw⁻ 9 (q77 c4) ∷
   rw 8 (q76 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw⁻ 6 (q79 c4) ∷
   rw 7 (q73 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   rw⁻ 8 (q80 c4) ∷
   rw 7 (q82 c4) ∷
   rw 11 (q83 c4) ∷
   rw 10 (q84 c4) ∷
   rw 9 (q85 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q86 c4) ∷
   rw⁻ 8 (q82 c4) ∷
   rw⁻ 6 (q87 c4) ∷
   rw⁻ 7 (q88 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 5 (q90 c4) ∷
   rw⁻ 2 (q70 c4) ∷
   rw 2 (q70 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   rw 5 (q76 c4) ∷
   rw⁻ 4 (q77 c4) ∷
   rw 3 (q76 c4) ∷
   rw⁻ 2 (q78 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   rw 2 (q73 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 4 (q73 c4) ∷
   rw⁻ 10 (q74 c4) ∷
   rw⁻ 9 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw⁻ 7 (q77 c4) ∷
   rw 6 (q76 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 6 (q80 c4) ∷
   rw 5 (q82 c4) ∷
   rw 9 (q83 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q85 c4) ∷
   rw 6 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw⁻ 5 (q88 c4) ∷
   rw⁻ 1 (q70 c4) ∷
   rw 0 (q91 c4) ∷
   rw 0 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw⁻ 0 (q94 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (Sb⁻0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Sb⁻0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (X))
  q96 : Ws → Eqn
  q96 c4 = eqn (Toff324 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ Toff324 ∷ []) (wl0211 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Sb0-1-3-2 ∷ X4 ∷ []) (X4 ∷ Sb0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X))
  q98 : Ws → Eqn
  q98 c4 = eqn (CS13 ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ []) (wl0212 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (CX23 ∷ Toff324 ∷ []) (Toff324 ∷ CX23 ∷ []) (wl0213 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ []) (wl0215 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (X4 ∷ CX23 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0216 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (X4 ∷ Bx0-1423 ∷ X4 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ []) (lem-Xb-box-at243243 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl0314 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp0067 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ []) (wl1414 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (CCZ124 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ []) (wl1415 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CS12 ∷ CCZ124 ∷ []) (CS12 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (wp1265 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Toff024 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ []) (wp0073 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CS12 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (wl1416 (lit c4))

-- F5-23 @132132: 112 steps
lem-F5-23-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-23-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 5 (q95 c4) ∷
   rw 4 (q96 c4) ∷
   rw 3 (q97 c4) ∷
   re 4 1 (CS13 ∷ []) ∷
   rw 4 (q98 c4) ∷
   re 7 1 (Sb0-1-3-2 ∷ []) ∷
   rw 2 (q96 c4) ∷
   rw⁻ 4 (q99 c4) ∷
   rw⁻ 5 (q100 c4) ∷
   rw⁻ 6 (q101 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 0 (q103 c4) ∷
   rw 9 (q70 c4) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 7 (q73 c4) ∷
   rw⁻ 13 (q74 c4) ∷
   rw⁻ 12 (q75 c4) ∷
   rw 11 (q76 c4) ∷
   rw⁻ 10 (q77 c4) ∷
   rw 9 (q76 c4) ∷
   rw⁻ 8 (q78 c4) ∷
   rw⁻ 7 (q79 c4) ∷
   rw 8 (q73 c4) ∷
   re 6 1 (CS13 ∷ []) ∷
   rw⁻ 6 (q89 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   rw⁻ 11 (q74 c4) ∷
   rw⁻ 10 (q75 c4) ∷
   rw 9 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw 7 (q76 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   rw 6 (q73 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 7 (q89 c4) ∷
   rw 6 (q76 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   rw 1 (q105 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 3 (q106 c4) ∷
   rw 2 (q76 c4) ∷
   rw⁻ 1 (q107 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 2 (q108 c4) ∷
   rw 7 (q72 c4) ∷
   rw⁻ 6 (q80 c4) ∷
   rw 5 (q82 c4) ∷
   rw 9 (q83 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q85 c4) ∷
   rw 6 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw 4 (q83 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 10 (q71 c4) ∷
   rw⁻ 9 (q73 c4) ∷
   rw⁻ 15 (q74 c4) ∷
   rw⁻ 14 (q75 c4) ∷
   rw 13 (q76 c4) ∷
   rw⁻ 12 (q77 c4) ∷
   rw 11 (q76 c4) ∷
   rw⁻ 10 (q78 c4) ∷
   rw⁻ 9 (q79 c4) ∷
   rw 10 (q73 c4) ∷
   rw⁻ 8 (q81 c4) ∷
   rw⁻ 7 (q104 c4) ∷
   rw⁻ 6 (q107 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw⁻ 4 (q73 c4) ∷
   rw⁻ 10 (q74 c4) ∷
   rw⁻ 9 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw⁻ 7 (q77 c4) ∷
   rw 6 (q76 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 5 (q109 c4) ∷
   rw 11 (q72 c4) ∷
   rw⁻ 10 (q80 c4) ∷
   rw 9 (q82 c4) ∷
   rw 13 (q83 c4) ∷
   rw 12 (q84 c4) ∷
   rw 11 (q85 c4) ∷
   rw 10 (q84 c4) ∷
   rw 9 (q86 c4) ∷
   rw⁻ 10 (q82 c4) ∷
   rw⁻ 8 (q87 c4) ∷
   rw 7 (q83 c4) ∷
   rw 6 (q90 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw 5 (q111 c4) ∷
   rw⁻ 1 (q70 c4) ∷
   rw 0 (q91 c4) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ []) (X0 ∷ []) (wl1420 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (wp1263 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp1267 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-K0 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-S0 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-S0 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-K0 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl1411 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K0 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S0 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-I c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-I c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS0 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-F4-K0-CS0 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0-CS0 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) [] (wp1274 c4)

-- ckt-Dinv: 73 steps
lem-ckt-Dinv : Ws → ⟪ (X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
lem-ckt-Dinv c4 = derive (X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw⁻ 8 (q113 c4) ∷
   rw 0 (q114 c4) ∷
   rw 4 (q115 c4) ∷
   rw⁻ 3 (q116 c4) ∷
   rw 8 (q115 c4) ∷
   rw⁻ 7 (q117 c4) ∷
   rw⁻ 6 (q116 c4) ∷
   rw 12 (q114 c4) ∷
   rw⁻ 11 (q118 c4) ∷
   rw⁻ 10 (q118 c4) ∷
   rw⁻ 9 (q119 c4) ∷
   rw⁻ 16 (q120 c4) ∷
   rw⁻ 15 (q121 c4) ∷
   rw⁻ 14 (q122 c4) ∷
   rw⁻ 13 (q122 c4) ∷
   rw⁻ 12 (q121 c4) ∷
   rw 23 (q114 c4) ∷
   rw 27 (q115 c4) ∷
   rw⁻ 26 (q116 c4) ∷
   rw 31 (q115 c4) ∷
   rw⁻ 30 (q117 c4) ∷
   rw⁻ 29 (q116 c4) ∷
   rw 35 (q114 c4) ∷
   rw⁻ 34 (q118 c4) ∷
   rw⁻ 33 (q118 c4) ∷
   rw⁻ 32 (q119 c4) ∷
   rw⁻ 39 (q120 c4) ∷
   rw⁻ 38 (q121 c4) ∷
   rw⁻ 37 (q122 c4) ∷
   rw⁻ 36 (q122 c4) ∷
   rw⁻ 35 (q121 c4) ∷
   rw 12 (q121 c4) ∷
   rw 9 (q119 c4) ∷
   rw 6 (q116 c4) ∷
   rw 3 (q116 c4) ∷
   rw 0 (q119 c4) ∷
   rw 13 (q122 c4) ∷
   rw 10 (q118 c4) ∷
   rw 7 (q117 c4) ∷
   rw 4 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 14 (q122 c4) ∷
   rw 11 (q118 c4) ∷
   rw 8 (q117 c4) ∷
   rw 5 (q117 c4) ∷
   rw 2 (q118 c4) ∷
   rw 15 (q121 c4) ∷
   rw 12 (q119 c4) ∷
   rw 9 (q116 c4) ∷
   rw 6 (q116 c4) ∷
   rw 3 (q119 c4) ∷
   rw 16 (q123 c4) ∷
   rw 13 (q124 c4) ∷
   rw 10 (q125 c4) ∷
   rw 7 (q125 c4) ∷
   rw 4 (q124 c4) ∷
   rw 17 (q126 c4) ∷
   rw 14 (q127 c4) ∷
   rw 11 (q128 c4) ∷
   rw 8 (q128 c4) ∷
   rw 5 (q127 c4) ∷
   rw 18 (q126 c4) ∷
   rw 15 (q127 c4) ∷
   rw 12 (q128 c4) ∷
   rw 9 (q128 c4) ∷
   rw 6 (q127 c4) ∷
   rw 19 (q126 c4) ∷
   rw 16 (q127 c4) ∷
   rw 13 (q128 c4) ∷
   rw 10 (q128 c4) ∷
   rw 7 (q127 c4) ∷
   rw 8 (q129 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (Bx2-4013 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (Toff301 ∷ []) (wl1380 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ Toff213 ∷ []) (wl1421 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ024 ∷ []) (wp0760 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CX40 ∷ Toff213 ∷ []) (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CS01⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS01⁻ ∷ []) (wl1422 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (Toff201 ∷ Toff213 ∷ []) (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (CCZ014 ∷ []) (Toff201 ∷ CCZ014 ∷ Toff201 ∷ []) (wp1275 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4))
  q142 : Ws → Eqn
  q142 c4 = eqn (Bx2-4013 ∷ Bx2-4013 ∷ []) [] (lem-box2-at0214203143 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (CCZ014 ∷ Toff301 ∷ CS34 ∷ []) (Toff301 ∷ CS34 ∷ CCZ014 ∷ []) (wp1276 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ014 ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (wp1277 c4)

-- S2-SBOX(0;2;43;1) @0213243140: 86 steps
lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 : Ws → ⟪ (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·2·43·1⟩-at0213243140 c4 = derive (Sb2-4-01-3 ∷ Sb2-4-01-3 ∷ []) (CCZ014 ∷ [])
  (re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   re 0 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 2 1 (CS34 ∷ []) ∷
   re 4 1 (CS34⁻ ∷ []) ∷
   rw 5 (q130 c4) ∷
   rw⁻ 4 (q131 c4) ∷
   rw 5 (q132 c4) ∷
   rw⁻ 6 (q131 c4) ∷
   rw 7 (q132 c4) ∷
   rw⁻ 4 (q130 c4) ∷
   rw 4 (q130 c4) ∷
   rw⁻ 3 (q133 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q64 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 4 (q133 c4) ∷
   rw⁻ 4 (q134 c4) ∷
   rw⁻ 6 (q133 c4) ∷
   rw⁻ 12 (q31 c4) ∷
   rw⁻ 11 (q46 c4) ∷
   rw 10 (q33 c4) ∷
   rw⁻ 9 (q63 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 7 (q133 c4) ∷
   rw⁻ 5 (q135 c4) ∷
   rw⁻ 8 (q134 c4) ∷
   rw 7 (q136 c4) ∷
   rw 11 (q43 c4) ∷
   rw 10 (q137 c4) ∷
   rw 9 (q138 c4) ∷
   rw 8 (q137 c4) ∷
   rw 7 (q40 c4) ∷
   rw⁻ 8 (q136 c4) ∷
   rw 6 (q139 c4) ∷
   rw⁻ 7 (q140 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw 3 (q130 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 3 (q141 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw 5 (q141 c4) ∷
   rw⁻ 2 (q130 c4) ∷
   rw 2 (q130 c4) ∷
   rw⁻ 1 (q133 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw 2 (q133 c4) ∷
   rw⁻ 2 (q134 c4) ∷
   rw⁻ 4 (q133 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q63 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q133 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw⁻ 6 (q134 c4) ∷
   rw 5 (q136 c4) ∷
   rw 9 (q43 c4) ∷
   rw 8 (q137 c4) ∷
   rw 7 (q138 c4) ∷
   rw 6 (q137 c4) ∷
   rw 5 (q40 c4) ∷
   rw⁻ 6 (q136 c4) ∷
   rw 4 (q139 c4) ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 1 (q130 c4) ∷
   rw 0 (q142 c4) ∷
   rw 0 (q143 c4) ∷
   rw 2 (q50 c4) ∷
   rw⁻ 0 (q144 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (Bx2-4301 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q148 : Ws → Eqn
  q148 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q149 : Ws → Eqn
  q149 c4 = eqn (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl1439 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (wp1292 c4)

-- F4-K3-CS2 @0213243140: 19 steps
lem-F4-K3-CS2-at0213243140 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at0213243140 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw 3 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 0 (q147 c4) ∷
   rw⁻ 1 (q149 c4) ∷
   rw 4 (q147 c4) ∷
   rw 3 (q148 c4) ∷
   rw 2 (q147 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw⁻ 0 (q146 c4) ∷
   rw⁻ 0 (q145 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ []) (wl1441 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wp1294 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (Toff201 ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wl1442 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (K1 ∷ CCZ234 ∷ []) (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ))
  q155 : Ws → Eqn
  q155 c4 = eqn (S0 ∷ CCZ234 ∷ []) (CCZ234 ∷ S0 ∷ []) (c₁ (S) (CCZ ↑))
  q156 : Ws → Eqn
  q156 c4 = eqn (CK01 ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wl1443 (lit c4))

-- F4-CS2-K3 @0213243140: 21 steps
lem-F4-CS2-K3-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at0213243140 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw⁻ 2 (q151 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw⁻ 2 (q152 c4) ∷
   rw 1 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 4 (q153 c4) ∷
   rw⁻ 3 (q154 c4) ∷
   rw⁻ 4 (q148 c4) ∷
   rw⁻ 5 (q155 c4) ∷
   rw⁻ 2 (q153 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw⁻ 2 (q148 c4) ∷
   rw⁻ 3 (q155 c4) ∷
   rw⁻ 4 (q146 c4) ∷
   rw⁻ 4 (q145 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 0 (q156 c4) ∷ []) Eq.refl
