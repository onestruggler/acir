{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD009 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D009 (Sᴰ : SD009) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-TOFF412 ; lem-comm-CS12-CCZ034 ; lem-comm-CS13-TOFF024 ; lem-comm-CS14-TOFF023 ; lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd02-TOFF134 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd12-TOFF034 ; lem-comm-CSd12-TOFF403 ; lem-comm-CSd13-TOFF024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-CCZ013 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX12-CCZ034 ; lem-comm-CX21-CCZ034 ; lem-comm-CX24-CCZ013 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ04-TOFF312 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034 ; lem-comm-CZ14-TOFF023 ; lem-comm-CZ24-TOFF013 ; lem-comm-TOFF013-CSd24 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF024-CSd13 ; lem-comm-TOFF204-CSd13 ; lem-comm-TOFF312-CSd04 ; lem-comm-TOFF412-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS04-CCZ123 ; lem-comm-CS04-TOFF312 ; lem-comm-CS13-TOFF204 ; lem-comm-CS14-CCZ023 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-CCZ023 ; lem-comm-CX40-CCZ123 ; lem-comm-CZ03-TOFF214 ; lem-comm-CZ12-TOFF304 ; lem-comm-CZ12-TOFF403 ; lem-comm-TOFF304-CSd12)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CSd14)

-- The lemmas of other derivation modules (DSig).
private
  lem-CXbc-box-at032032 : Ws → St 129
  lem-CXbc-box-at032032 = pickᴰ 0 Sᴰ
  lem-CXbc-box-at04203243 : Ws → St 130
  lem-CXbc-box-at04203243 = pickᴰ 1 Sᴰ
  lem-CXbc-box-at13243142 : Ws → St 131
  lem-CXbc-box-at13243142 = pickᴰ 2 Sᴰ
  lem-CXbc-box-at13243241 : Ws → St 132
  lem-CXbc-box-at13243241 = pickᴰ 3 Sᴰ
  lem-CXbc-box-at14233142 : Ws → St 133
  lem-CXbc-box-at14233142 = pickᴰ 4 Sᴰ
  lem-CXcb-box-at032032 : Ws → St 134
  lem-CXcb-box-at032032 = pickᴰ 5 Sᴰ
  lem-CXcb-box-at04203243 : Ws → St 135
  lem-CXcb-box-at04203243 = pickᴰ 6 Sᴰ
  lem-CXcb-box-at13243142 : Ws → St 136
  lem-CXcb-box-at13243142 = pickᴰ 7 Sᴰ
  lem-CXcb-box-at13243241 : Ws → St 137
  lem-CXcb-box-at13243241 = pickᴰ 8 Sᴰ
  lem-CXcb-box-at14233142 : Ws → St 138
  lem-CXcb-box-at14233142 = pickᴰ 9 Sᴰ
  lem-VPQ-at021021 : Ws → St 139
  lem-VPQ-at021021 = pickᴰ 10 Sᴰ
  lem-VPQ-at03102132 : Ws → St 140
  lem-VPQ-at03102132 = pickᴰ 11 Sᴰ
  lem-VPQ-at0410213243 : Ws → St 141
  lem-VPQ-at0410213243 = pickᴰ 12 Sᴰ
  lem-VPQ-at04203243 : Ws → St 142
  lem-VPQ-at04203243 = pickᴰ 13 Sᴰ
  lem-VPQ-at13243142 : Ws → St 143
  lem-VPQ-at13243142 = pickᴰ 14 Sᴰ
  lem-VPQ-at13243241 : Ws → St 144
  lem-VPQ-at13243241 = pickᴰ 15 Sᴰ
  lem-VPQ-at14233142 : Ws → St 145
  lem-VPQ-at14233142 = pickᴰ 16 Sᴰ
  lem-box-tQ : Ws → St 146
  lem-box-tQ = pickᴰ 17 Sᴰ
  lem-box-tQ-at0210243143 : Ws → St 147
  lem-box-tQ-at0210243143 = pickᴰ 18 Sᴰ
  lem-box-tQ-at0214203143 : Ws → St 148
  lem-box-tQ-at0214203143 = pickᴰ 19 Sᴰ
  lem-box-tQ-at0214213043 : Ws → St 149
  lem-box-tQ-at0214213043 = pickᴰ 20 Sᴰ
  lem-box-tQ-at0310243142 : Ws → St 150
  lem-box-tQ-at0310243142 = pickᴰ 21 Sᴰ
  lem-box-tQ-at0330 : Ws → St 151
  lem-box-tQ-at0330 = pickᴰ 22 Sᴰ
  lem-box-tQ-at043043 : Ws → St 152
  lem-box-tQ-at043043 = pickᴰ 23 Sᴰ
  lem-box-tQ-at1221 : Ws → St 153
  lem-box-tQ-at1221 = pickᴰ 24 Sᴰ
  lem-box-tQ-at122331 : Ws → St 154
  lem-box-tQ-at122331 = pickᴰ 25 Sᴰ
  lem-box-tQ-at12243143 : Ws → St 155
  lem-box-tQ-at12243143 = pickᴰ 26 Sᴰ
  lem-box-tQ-at122441 : Ws → St 156
  lem-box-tQ-at122441 = pickᴰ 27 Sᴰ
  lem-box-tQ-at132132 : Ws → St 157
  lem-box-tQ-at132132 = pickᴰ 28 Sᴰ
  lem-box-tQ-at13213442 : Ws → St 158
  lem-box-tQ-at13213442 = pickᴰ 29 Sᴰ
  lem-box-tQ-at1331 : Ws → St 159
  lem-box-tQ-at1331 = pickᴰ 30 Sᴰ
  lem-box-tQ-at133441 : Ws → St 160
  lem-box-tQ-at133441 = pickᴰ 31 Sᴰ
  lem-box-tQ-at2332 : Ws → St 161
  lem-box-tQ-at2332 = pickᴰ 32 Sᴰ
  lem-box-tQ-at243243 : Ws → St 162
  lem-box-tQ-at243243 = pickᴰ 33 Sᴰ
  lem-box-tQ-at3443 : Ws → St 163
  lem-box-tQ-at3443 = pickᴰ 34 Sᴰ
  lem-tP : Ws → St 164
  lem-tP = pickᴰ 35 Sᴰ
  lem-tP-at0110 : Ws → St 165
  lem-tP-at0110 = pickᴰ 36 Sᴰ
  lem-tP-at0210243143 : Ws → St 166
  lem-tP-at0210243143 = pickᴰ 37 Sᴰ
  lem-tP-at0214213043 : Ws → St 167
  lem-tP-at0214213043 = pickᴰ 38 Sᴰ
  lem-tP-at0310243142 : Ws → St 168
  lem-tP-at0310243142 = pickᴰ 39 Sᴰ
  lem-tP-at0314203142 : Ws → St 169
  lem-tP-at0314203142 = pickᴰ 40 Sᴰ
  lem-tP-at0330 : Ws → St 170
  lem-tP-at0330 = pickᴰ 41 Sᴰ
  lem-tP-at043043 : Ws → St 171
  lem-tP-at043043 = pickᴰ 42 Sᴰ
  lem-tP-at1221 : Ws → St 172
  lem-tP-at1221 = pickᴰ 43 Sᴰ
  lem-tP-at122331 : Ws → St 173
  lem-tP-at122331 = pickᴰ 44 Sᴰ
  lem-tP-at122441 : Ws → St 174
  lem-tP-at122441 = pickᴰ 45 Sᴰ
  lem-tP-at132132 : Ws → St 175
  lem-tP-at132132 = pickᴰ 46 Sᴰ
  lem-tP-at13213442 : Ws → St 176
  lem-tP-at13213442 = pickᴰ 47 Sᴰ
  lem-tP-at1331 : Ws → St 177
  lem-tP-at1331 = pickᴰ 48 Sᴰ
  lem-tP-at2332 : Ws → St 178
  lem-tP-at2332 = pickᴰ 49 Sᴰ
  lem-tP-at243243 : Ws → St 179
  lem-tP-at243243 = pickᴰ 50 Sᴰ
  lem-tP-at3443 : Ws → St 180
  lem-tP-at3443 = pickᴰ 51 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) (wl 158 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) (wp 5 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (S0⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))
  q5 : Ws → Eqn
  q5 c4 = eqn (S0 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS12⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))
  q7 : Ws → Eqn
  q7 c4 = eqn (S0⁻ ∷ S0 ∷ []) [] (wl 159 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (S0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS12⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (S0⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS))

-- VPQ: 14 steps
lem-VPQ : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ c4 = derive (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ012 ∷ Toff012 ∷ CZ12 ∷ []) (Toff012 ∷ CCZ012 ∷ []) (wl 163 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CZ12 ∷ Toff034 ∷ []) (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wl 164 (lit c4))

-- t-cP: 5 steps
lem-t-cP : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-t-cP c4 = derive (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 3 (q8 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = eqn (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp 15 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ []) (wl 176 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS13⁻ ∷ []) (wl 177 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Toff204 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS13⁻ ∷ S2 ∷ []) (S2 ∷ CS13⁻ ∷ []) (wl 178 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CS04⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04⁻ ∷ []) (wp 16 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (S2⁻ ∷ S2 ∷ []) [] (wl 179 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS04⁻ ∷ S2 ∷ []) (S2 ∷ CS04⁻ ∷ []) (wp 17 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS04⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CS04⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS04⁻ ∷ []) (wp 18 c4)

-- VPQ @0210243143: 14 steps
lem-VPQ-at0210243143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at0210243143 c4 = derive (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q15 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 0 (q16 c4) ∷
   rw 2 (q15 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp 27 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CZ04 ∷ Toff213 ∷ []) (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp 28 c4)

-- t-cP @0210243143: 5 steps
lem-t-cP-at0210243143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-t-cP-at0210243143 c4 = derive (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q22 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 3 (q22 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) (wp 50 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) (wl 201 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑))
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS14⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS14⁻ ∷ []) (wl 202 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (S0 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS14⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (S0⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))

-- VPQ @243243: 14 steps
lem-VPQ-at243243 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at243243 c4 = derive (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q34 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 0 (q30 c4) ∷
   rw 2 (q29 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ []) (wp 58 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CZ14 ∷ Toff023 ∷ []) (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (wp 59 c4)

-- t-cP @243243: 5 steps
lem-t-cP-at243243 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-t-cP-at243243 c4 = derive (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw 3 (q35 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) (wp 79 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) (wl 227 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (S0⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q45 : Ws → Eqn
  q45 c4 = eqn (Toff024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (S0 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q47 : Ws → Eqn
  q47 c4 = eqn (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) (wl 228 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (S0 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))
  q50 : Ws → Eqn
  q50 c4 = eqn (CS24⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (S0⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))

-- VPQ @122441: 14 steps
lem-VPQ-at122441 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at122441 c4 = derive (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q42 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   rw 3 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 0 (q47 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw⁻ 3 (q51 c4) ∷
   rw 0 (q43 c4) ∷
   rw 2 (q42 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ []) (wp 85 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CZ24 ∷ Toff013 ∷ []) (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (wp 86 c4)

-- t-cP @122441: 5 steps
lem-t-cP-at122441 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-t-cP-at122441 c4 = derive (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q52 c4) ∷
   rw 2 (q53 c4) ∷
   rw 1 (q48 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw 3 (q48 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CX32 ∷ Toff012 ∷ []) (Toff012 ∷ CX32 ∷ Toff013 ∷ []) (wl 250 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ034 ∷ Toff013 ∷ CCZ134 ∷ []) (Toff013 ∷ CCZ034 ∷ []) (wp 100 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ034 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ []) (wp 101 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl 166 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) (wp 102 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CX13 ∷ Toff012 ∷ []) (Toff012 ∷ CX13 ∷ []) (wl 251 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))
  q63 : Ws → Eqn
  q63 c4 = eqn (Toff012 ∷ Toff013 ∷ []) (Toff013 ∷ Toff012 ∷ []) (wl 252 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CX32 ∷ Toff013 ∷ Toff013 ∷ []) (CX32 ∷ []) (wl 253 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) (wp 103 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ134 ∷ []) (CX32 ∷ CCZ134 ∷ CX32 ∷ []) (wl 254 (lit c4))

-- CXcb-box: 18 steps
lem-CXcb-box : Ws → ⟪ (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box c4 = derive (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q56 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 1 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw 8 (q60 c4) ∷
   rw 7 (q61 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw⁻ 3 (q63 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (CX23 ∷ Toff012 ∷ []) (Toff012 ∷ CX23 ∷ []) (wl 255 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (CX23 ∷ CCZ034 ∷ []) (wp 104 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ024 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp 105 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl 256 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) (wp 106 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) (wp 107 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp 108 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) (wp 109 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX23 ∷ []) (wp 110 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ124 ∷ []) (CX23 ∷ CCZ124 ∷ CX23 ∷ []) (wl 257 (lit c4))

-- CXbc-box: 17 steps
lem-CXbc-box : Ws → ⟪ (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box c4 = derive (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw 3 (q69 c4) ∷
   rw 2 (q67 c4) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 8 (q72 c4) ∷
   rw⁻ 7 (q73 c4) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 5 (q74 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ []) (wp 112 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CCZ034 ∷ CZ34 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff034 ∷ []) (wp 113 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Toff012 ∷ CZ34 ∷ []) (CZ34 ∷ Toff012 ∷ []) (c₃ (Toff) (CZ))
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ034 ∷ []) (CZ34 ∷ CCZ034 ∷ CZ34 ∷ []) (wp 114 c4)

-- P-box: 8 steps
lem-P-box : Ws → ⟪ (Toff034 ∷ Bx0-1234 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-P-box c4 = derive (Toff034 ∷ Bx0-1234 ∷ Toff034 ∷ []) (Bx0-1234 ∷ [])
  (rw 1 (q55 c4) ∷
   rw⁻ 0 (q8 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx0-2134 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at1221 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (CX13 ∷ CCZ034 ∷ []) (wp 121 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ014 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp 122 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl 271 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CX21 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ034 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ034 ∷ []) (wp 123 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) (wp 124 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CX13 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX13 ∷ []) (wp 125 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ124 ∷ []) (CX13 ∷ CCZ124 ∷ CX13 ∷ []) (wl 272 (lit c4))

-- CXbc-box @1221: 17 steps
lem-CXbc-box-at1221 : Ws → ⟪ (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at1221 c4 = derive (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  (rw 1 (q82 c4) ∷
   rw 0 (q61 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw 2 (q61 c4) ∷
   rw 5 (q85 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw 8 (q86 c4) ∷
   rw⁻ 7 (q87 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 5 (q71 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 0 (q82 c4) ∷
   rw⁻ 1 (q90 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = eqn (CX31 ∷ Toff012 ∷ []) (Toff012 ∷ CX31 ∷ Toff023 ∷ []) (wl 273 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) (Toff023 ∷ CCZ034 ∷ []) (wp 126 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ034 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ []) (wp 127 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl 274 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (CS24 ∷ Toff012 ∷ []) (Toff012 ∷ CS24 ∷ []) (wp 128 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Toff012 ∷ Toff023 ∷ []) (Toff023 ∷ Toff012 ∷ []) (wl 275 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (CX31 ∷ Toff023 ∷ Toff023 ∷ []) (CX31 ∷ []) (wl 276 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ []) (wp 129 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ234 ∷ []) (CX31 ∷ CCZ234 ∷ CX31 ∷ []) (wl 277 (lit c4))

-- CXcb-box @1221: 18 steps
lem-CXcb-box-at1221 : Ws → ⟪ (CX31 ∷ Bx0-2134 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at1221 c4 = derive (CX31 ∷ Bx0-2134 ∷ CX31 ∷ []) (Bx0-2134 ∷ CCZ234 ∷ [])
  (rw 1 (q82 c4) ∷
   rw 0 (q91 c4) ∷
   rw⁻ 2 (q92 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw 4 (q94 c4) ∷
   rw 8 (q95 c4) ∷
   rw 7 (q67 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 5 (q94 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   rw 2 (q91 c4) ∷
   rw 3 (q97 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q93 c4) ∷
   rw⁻ 0 (q82 c4) ∷
   rw⁻ 1 (q99 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP-at1221 c4)

-- P-box @1221: 8 steps
lem-P-box-at1221 : Ws → ⟪ (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-P-box-at1221 c4 = derive (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) (Bx0-2134 ∷ [])
  (rw 1 (q82 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 3 (q100 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 0 (q82 c4) ∷ []) Eq.refl

-- VPQ @1221: 14 steps
lem-VPQ-at1221 : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at1221 c4 = derive (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q100 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at2332 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at2332 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ []) (wp 132 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) (wp 133 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ024 ∷ []) (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) (wp 134 c4)

-- P-box @2332: 8 steps
lem-P-box-at2332 : Ws → ⟪ (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-P-box-at2332 c4 = derive (Toff024 ∷ Bx0-1324 ∷ Toff024 ∷ []) (Bx0-1324 ∷ [])
  (rw 1 (q101 c4) ∷
   rw⁻ 0 (q102 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw⁻ 0 (q101 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CS13⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4))

-- VPQ @2332: 14 steps
lem-VPQ-at2332 : Ws → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at2332 c4 = derive (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q43 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 3 (q51 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q49 c4) ∷
   rw 0 (q47 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q46 c4) ∷
   rw 2 (q107 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 0 (q42 c4) ∷
   rw 2 (q43 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (CX41 ∷ CX14 ∷ CX41 ∷ []) (Sw14 ∷ []) (wl 300 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) (Bx0-3412 ∷ CCZ234 ∷ []) (lem-CXbc-box-at13243142 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ234 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl 301 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CX14 ∷ Bx0-3412 ∷ CX14 ∷ []) (Bx0-3412 ∷ CCZ123 ∷ []) (lem-CXcb-box-at13243142 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ234 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ []) (wl 302 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl 303 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) (wl 304 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))

-- SWbc-box @13243142: 11 steps
lem-SWbc-box-at13243142 : Ws → ⟪ (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-SWbc-box-at13243142 c4 = derive (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (Bx0-3412 ∷ [])
  (rw⁻ 0 (q108 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw 2 (q109 c4) ∷
   rw 3 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 4 (q112 c4) ∷
   rw 3 (q113 c4) ∷
   rw 2 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw 0 (q109 c4) ∷
   rw 1 (q115 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ []) (lem-tP-at122331 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ []) (wp 158 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (CCZ014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) (wp 159 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (CCZ014 ∷ []) (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) (wp 160 c4)

-- P-box @122331: 8 steps
lem-P-box-at122331 : Ws → ⟪ (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-P-box-at122331 c4 = derive (Toff014 ∷ Bx0-2314 ∷ Toff014 ∷ []) (Bx0-2314 ∷ [])
  (rw 1 (q116 c4) ∷
   rw⁻ 0 (q117 c4) ∷
   rw⁻ 1 (q118 c4) ∷
   rw⁻ 3 (q117 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 3 (q120 c4) ∷
   rw⁻ 0 (q116 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Toff023 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CS23⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4))

-- VPQ @122331: 14 steps
lem-VPQ-at122331 : Ws → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at122331 c4 = derive (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 3 (q38 c4) ∷
   rw 2 (q121 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q34 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q117 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   rw 2 (q122 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 0 (q29 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (CX42 ∷ CX24 ∷ CX42 ∷ []) (Sw24 ∷ []) (wl 316 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CX42 ∷ Bx0-3421 ∷ CX42 ∷ []) (Bx0-3421 ∷ CCZ134 ∷ []) (lem-CXbc-box-at13243241 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ134 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl 317 (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (CX24 ∷ Bx0-3421 ∷ CX24 ∷ []) (Bx0-3421 ∷ CCZ123 ∷ []) (lem-CXcb-box-at13243241 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ134 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ []) (wl 318 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl 319 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wl 320 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl 321 (lit c4))

-- SWbc-box @13243241: 11 steps
lem-SWbc-box-at13243241 : Ws → ⟪ (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-SWbc-box-at13243241 c4 = derive (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (Bx0-3421 ∷ [])
  (rw⁻ 0 (q123 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   rw 2 (q124 c4) ∷
   rw 3 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw 4 (q127 c4) ∷
   rw 3 (q128 c4) ∷
   rw 2 (q128 c4) ∷
   rw 3 (q129 c4) ∷
   rw 0 (q124 c4) ∷
   rw 1 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Bx0-3124 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at132132 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at132132 c4)

-- P-box @132132: 8 steps
lem-P-box-at132132 : Ws → ⟪ (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-P-box-at132132 c4 = derive (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) (Bx0-3124 ∷ [])
  (rw 1 (q131 c4) ∷
   rw⁻ 0 (q132 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw⁻ 0 (q131 c4) ∷ []) Eq.refl

-- VPQ @132132: 14 steps
lem-VPQ-at132132 : Ws → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at132132 c4 = derive (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q43 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 3 (q51 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q49 c4) ∷
   rw 0 (q47 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q46 c4) ∷
   rw 2 (q107 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 0 (q42 c4) ∷
   rw 2 (q43 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at12243143 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (CX41 ∷ Toff024 ∷ []) (Toff024 ∷ CX41 ∷ []) (wp 181 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (CX41 ∷ CCZ013 ∷ []) (wp 182 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp 183 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl 245 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) (wl 324 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (CX24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (CCZ013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ013 ∷ []) (wp 184 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ013 ∷ CS34 ∷ []) (CS34 ∷ CCZ013 ∷ []) (wp 185 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) (wp 186 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX41 ∷ []) (wp 187 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ234 ∷ []) (CX41 ∷ CCZ234 ∷ CX41 ∷ []) (wl 295 (lit c4))

-- CXbc-box @12243143: 17 steps
lem-CXbc-box-at12243143 : Ws → ⟪ (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at12243143 c4 = derive (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) (Bx0-2413 ∷ CCZ234 ∷ [])
  (rw 1 (q133 c4) ∷
   rw 0 (q134 c4) ∷
   rw⁻ 1 (q135 c4) ∷
   rw 3 (q136 c4) ∷
   rw 2 (q134 c4) ∷
   rw 5 (q137 c4) ∷
   rw⁻ 9 (q138 c4) ∷
   rw 8 (q139 c4) ∷
   rw⁻ 7 (q140 c4) ∷
   rw 6 (q139 c4) ∷
   rw⁻ 5 (q141 c4) ∷
   rw⁻ 6 (q137 c4) ∷
   rw⁻ 4 (q142 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw 4 (q143 c4) ∷
   rw⁻ 0 (q133 c4) ∷
   rw⁻ 1 (q144 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = eqn (CX14 ∷ Toff024 ∷ []) (Toff024 ∷ CX14 ∷ Toff012 ∷ []) (wp 188 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (Toff012 ∷ CCZ013 ∷ []) (wl 325 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ []) (wp 189 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl 326 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ []) (wp 190 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (CX21 ∷ Toff024 ∷ []) (Toff024 ∷ CX21 ∷ []) (wp 191 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (CS13 ∷ Toff024 ∷ []) (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (Toff012 ∷ Toff024 ∷ []) (Toff024 ∷ Toff012 ∷ []) (wp 192 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (CX14 ∷ Toff012 ∷ Toff012 ∷ []) (CX14 ∷ []) (wp 193 c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) (wl 327 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (CCZ123 ∷ []) (CX14 ∷ CCZ123 ∷ CX14 ∷ []) (wl 299 (lit c4))

-- CXcb-box @12243143: 18 steps
lem-CXcb-box-at12243143 : Ws → ⟪ (CX14 ∷ Bx0-2413 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at12243143 c4 = derive (CX14 ∷ Bx0-2413 ∷ CX14 ∷ []) (Bx0-2413 ∷ CCZ123 ∷ [])
  (rw 1 (q133 c4) ∷
   rw 0 (q145 c4) ∷
   rw⁻ 2 (q146 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 4 (q148 c4) ∷
   rw 8 (q149 c4) ∷
   rw 7 (q150 c4) ∷
   rw 6 (q107 c4) ∷
   rw 5 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 5 (q148 c4) ∷
   rw 3 (q152 c4) ∷
   rw 2 (q145 c4) ∷
   rw 3 (q153 c4) ∷
   rw⁻ 4 (q154 c4) ∷
   rw⁻ 3 (q147 c4) ∷
   rw⁻ 0 (q133 c4) ∷
   rw⁻ 1 (q155 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = eqn (CX31 ∷ CX13 ∷ CX31 ∷ []) (Sw13 ∷ []) (wl 335 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (CX31 ∷ Bx0-4312 ∷ CX31 ∷ []) (Bx0-4312 ∷ CCZ234 ∷ []) (lem-CXbc-box-at14233142 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl 281 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (CX13 ∷ Bx0-4312 ∷ CX13 ∷ []) (Bx0-4312 ∷ CCZ124 ∷ []) (lem-CXcb-box-at14233142 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ234 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ []) (wl 336 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl 279 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) (wl 337 (lit c4))

-- SWbc-box @14233142: 11 steps
lem-SWbc-box-at14233142 : Ws → ⟪ (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-SWbc-box-at14233142 c4 = derive (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (Bx0-4312 ∷ [])
  (rw⁻ 0 (q156 c4) ∷
   rw⁻ 4 (q156 c4) ∷
   rw 2 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw 1 (q159 c4) ∷
   rw 4 (q160 c4) ∷
   rw 3 (q161 c4) ∷
   rw 2 (q161 c4) ∷
   rw 3 (q162 c4) ∷
   rw 0 (q157 c4) ∷
   rw 1 (q115 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wl 162 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (lem-VPQ-at14233142 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl 341 (lit c4))

-- QVQ @14233142: 3 steps
lem-QVQ-at14233142 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at14233142 c4 = derive (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q163 c4) ∷
   rw⁻ 1 (q164 c4) ∷
   rw 4 (q165 c4) ∷ []) Eq.refl

private
  q166 : Ws → Eqn
  q166 c4 = eqn (Bx0-3142 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at13213442 c4)

-- P-box @13213442: 8 steps
lem-P-box-at13213442 : Ws → ⟪ (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-P-box-at13213442 c4 = derive (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) (Bx0-3142 ∷ [])
  (rw 1 (q166 c4) ∷
   rw⁻ 0 (q167 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw⁻ 3 (q167 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw⁻ 0 (q166 c4) ∷ []) Eq.refl

-- VPQ @13213442: 14 steps
lem-VPQ-at13213442 : Ws → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at13213442 c4 = derive (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q43 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 3 (q51 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q49 c4) ∷
   rw 0 (q47 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q46 c4) ∷
   rw 2 (q107 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 0 (q42 c4) ∷
   rw 2 (q43 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (Bx0-3214 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ []) (lem-tP-at1331 c4)

-- P-box @1331: 8 steps
lem-P-box-at1331 : Ws → ⟪ (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-P-box-at1331 c4 = derive (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) (Bx0-3214 ∷ [])
  (rw 1 (q168 c4) ∷
   rw⁻ 0 (q169 c4) ∷
   rw⁻ 1 (q118 c4) ∷
   rw⁻ 3 (q169 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 3 (q120 c4) ∷
   rw⁻ 0 (q168 c4) ∷ []) Eq.refl

-- VPQ @1331: 14 steps
lem-VPQ-at1331 : Ws → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at1331 c4 = derive (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 3 (q38 c4) ∷
   rw 2 (q121 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q34 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q169 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   rw 2 (q122 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 0 (q29 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = eqn (S0 ∷ Toff012 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (wl 347 (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl 348 (lit c4))
  q172 : Ws → Eqn
  q172 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp 3 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) (wp 221 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (CCZ034 ∷ S0 ∷ []) (S0 ∷ CCZ034 ∷ []) (wp 222 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (wl 349 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (S0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (S0 ∷ []) (wl 350 (lit c4))

-- Su-box: 17 steps
lem-Su-box : Ws → ⟪ (S0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box c4 = derive (S0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q170 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q175 c4) ∷
   rw⁻ 1 (q176 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q178 c4) ∷
   rw⁻ 3 (q176 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (S0⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl 351 (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ034 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ034 ∷ []) (wp 223 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ []) (wl 352 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (S0⁻ ∷ []) (wl 353 (lit c4))

-- Sdu-box: 17 steps
lem-Sdu-box : Ws → ⟪ (S0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ
lem-Sdu-box c4 = derive (S0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0⁻ ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q179 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q174 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q181 c4) ∷
   rw 2 (q179 c4) ∷
   rw 3 (q182 c4) ∷
   rw⁻ 3 (q180 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = eqn (CS01 ∷ Toff012 ∷ []) (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) (wl 354 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) (wp 1 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (CS01 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS01 ∷ []) (wl 355 (lit c4))

-- CSu-box-1: 17 steps
lem-CSu-box-1 : Ws → ⟪ (CS01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS01 ∷ []) ⟫ʷ
lem-CSu-box-1 c4 = derive (CS01 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS01 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q183 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q175 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q183 c4) ∷
   rw 3 (q185 c4) ∷
   rw⁻ 3 (q184 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q186 : Ws → Eqn
  q186 c4 = eqn (CS01⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl 356 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (CCZ034 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ034 ∷ []) (wp 120 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (CS01⁻ ∷ []) (wl 357 (lit c4))

-- CSdu-box-1: 17 steps
lem-CSdu-box-1 : Ws → ⟪ (CS01⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CSdu-box-1 c4 = derive (CS01⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS01⁻ ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q186 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q174 c4) ∷
   rw⁻ 1 (q187 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q181 c4) ∷
   rw 2 (q186 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 3 (q187 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = eqn (CZ01 ∷ Toff012 ∷ []) (Toff012 ∷ CZ01 ∷ CZ12 ∷ []) (wl 358 (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CCZ034 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ034 ∷ []) (wp 224 c4)
  q192 : Ws → Eqn
  q192 c4 = eqn (CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ []) (wl 359 (lit c4))
  q193 : Ws → Eqn
  q193 c4 = eqn (CZ01 ∷ CZ12 ∷ CZ12 ∷ []) (CZ01 ∷ []) (wl 360 (lit c4))

-- CZu-box-1: 9 steps
lem-CZu-box-1 : Ws → ⟪ (CZ01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZu-box-1 c4 = derive (CZ01 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ01 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q189 c4) ∷
   rw 2 (q190 c4) ∷
   rw⁻ 1 (q191 c4) ∷
   rw 3 (q192 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q193 c4) ∷
   rw⁻ 3 (q191 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q194 : Ws → Eqn
  q194 c4 = eqn (CX10 ∷ Toff012 ∷ []) (Toff012 ∷ CX10 ∷ []) (wl 361 (lit c4))
  q195 : Ws → Eqn
  q195 c4 = eqn (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (CX10 ∷ CCZ034 ∷ []) (wp 225 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (CX10 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX10 ∷ []) (wp 226 c4)

-- CXu-box-1: 15 steps
lem-CXu-box-1 : Ws → ⟪ (CX10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ
lem-CXu-box-1 c4 = derive (CX10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX10 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q194 c4) ∷
   rw⁻ 1 (q195 c4) ∷
   rw 3 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 2 (q194 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw⁻ 3 (q195 c4) ∷
   rw 4 (q196 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = eqn (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (wl 368 (lit c4))
  q198 : Ws → Eqn
  q198 c4 = eqn (CS02 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS02 ∷ []) (wl 369 (lit c4))

-- CSu-box-2: 17 steps
lem-CSu-box-2 : Ws → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-2 c4 = derive (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q197 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q175 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q197 c4) ∷
   rw 3 (q198 c4) ∷
   rw⁻ 3 (q172 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (CS02⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wl 370 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) (wp 2 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (CS02⁻ ∷ []) (wl 371 (lit c4))

-- CSdu-box-2: 17 steps
lem-CSdu-box-2 : Ws → ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2 c4 = derive (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q199 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q174 c4) ∷
   rw⁻ 1 (q200 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q181 c4) ∷
   rw 2 (q199 c4) ∷
   rw 3 (q201 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = eqn (CZ02 ∷ Toff012 ∷ []) (Toff012 ∷ CZ02 ∷ CZ12 ∷ []) (wl 372 (lit c4))
  q203 : Ws → Eqn
  q203 c4 = eqn (CCZ034 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ034 ∷ []) (wp 227 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (CZ02 ∷ CZ12 ∷ CZ12 ∷ []) (CZ02 ∷ []) (wl 373 (lit c4))

-- CZu-box-2: 9 steps
lem-CZu-box-2 : Ws → ⟪ (CZ02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ []) ⟫ʷ
lem-CZu-box-2 c4 = derive (CZ02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q202 c4) ∷
   rw 2 (q190 c4) ∷
   rw⁻ 1 (q203 c4) ∷
   rw 3 (q192 c4) ∷
   rw 2 (q202 c4) ∷
   rw 3 (q204 c4) ∷
   rw⁻ 3 (q203 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = eqn (CX20 ∷ Toff012 ∷ []) (Toff012 ∷ CX20 ∷ []) (wl 374 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (CX20 ∷ CCZ034 ∷ []) (wp 228 c4)
  q207 : Ws → Eqn
  q207 c4 = eqn (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX20 ∷ []) (wp 229 c4)

-- CXu-box-2: 15 steps
lem-CXu-box-2 : Ws → ⟪ (CX20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX20 ∷ []) ⟫ʷ
lem-CXu-box-2 c4 = derive (CX20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX20 ∷ [])
  (rw 1 (q55 c4) ∷
   rw 0 (q205 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 3 (q94 c4) ∷
   rw 7 (q95 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 4 (q94 c4) ∷
   rw 2 (q205 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q208 : Ws → Eqn
  q208 c4 = eqn (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) (Toff102 ∷ CCZ012 ∷ []) (wl 397 (lit c4))
  q209 : Ws → Eqn
  q209 c4 = eqn (CS34⁻ ∷ S1 ∷ Toff134 ∷ S1⁻ ∷ []) (Toff134 ∷ CCZ134 ∷ []) (wl 398 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (S1⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S1⁻ ∷ []) (c₂ ((S • S • S) ↑) ((CS • CS • CS) ↑))
  q211 : Ws → Eqn
  q211 c4 = eqn (Toff102 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))
  q212 : Ws → Eqn
  q212 c4 = eqn (S1 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S1 ∷ []) (c₂ (S ↑) ((CS • CS • CS) ↑))
  q213 : Ws → Eqn
  q213 c4 = eqn (CS02⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (CS • CS • CS))
  q214 : Ws → Eqn
  q214 c4 = eqn (S1⁻ ∷ S1 ∷ []) [] (wl 399 (lit c4))
  q215 : Ws → Eqn
  q215 c4 = eqn (Toff102 ∷ Toff134 ∷ []) (Toff134 ∷ Toff102 ∷ []) (lem-tP-at0110 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (CS02⁻ ∷ S1 ∷ []) (S1 ∷ CS02⁻ ∷ []) (wl 400 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (CS02⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF134 (lit c4))
  q218 : Ws → Eqn
  q218 c4 = eqn (CS02⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ CS02⁻ ∷ []) (wl 401 (lit c4))

-- VPQ @0110: 14 steps
lem-VPQ-at0110 : Ws → ⟪ (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0110 c4 = derive (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) (Toff134 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q208 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   rw 3 (q210 c4) ∷
   rw 2 (q211 c4) ∷
   rw 1 (q212 c4) ∷
   rw 0 (q213 c4) ∷
   rw 4 (q214 c4) ∷
   rw 3 (q215 c4) ∷
   rw⁻ 4 (q214 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q217 c4) ∷
   rw 3 (q218 c4) ∷
   rw 0 (q209 c4) ∷
   rw 2 (q208 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = eqn (Bx0-3241 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at133441 c4)
  q220 : Ws → Eqn
  q220 c4 = eqn (CX24 ∷ Toff023 ∷ []) (Toff023 ∷ CX24 ∷ []) (wp 263 c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) (CX24 ∷ CCZ014 ∷ []) (wp 264 c4)
  q222 : Ws → Eqn
  q222 c4 = eqn (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl 404 (lit c4))
  q223 : Ws → Eqn
  q223 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wl 314 (lit c4))
  q224 : Ws → Eqn
  q224 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (CX32 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4))
  q226 : Ws → Eqn
  q226 c4 = eqn (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ []) (wp 265 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp 67 c4)
  q228 : Ws → Eqn
  q228 c4 = eqn (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) (wp 167 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (CX24 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX24 ∷ []) (wp 266 c4)
  q230 : Ws → Eqn
  q230 c4 = eqn (CCZ123 ∷ []) (CX24 ∷ CCZ123 ∷ CX24 ∷ []) (wl 315 (lit c4))

-- CXbc-box @133441: 17 steps
lem-CXbc-box-at133441 : Ws → ⟪ (CX24 ∷ Bx0-3241 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at133441 c4 = derive (CX24 ∷ Bx0-3241 ∷ CX24 ∷ []) (Bx0-3241 ∷ CCZ123 ∷ [])
  (rw 1 (q219 c4) ∷
   rw 0 (q220 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 3 (q222 c4) ∷
   rw 2 (q220 c4) ∷
   rw 5 (q223 c4) ∷
   rw⁻ 9 (q224 c4) ∷
   rw 8 (q225 c4) ∷
   rw⁻ 7 (q226 c4) ∷
   rw 6 (q225 c4) ∷
   rw⁻ 5 (q227 c4) ∷
   rw⁻ 6 (q223 c4) ∷
   rw 4 (q228 c4) ∷
   rw⁻ 3 (q221 c4) ∷
   rw 4 (q229 c4) ∷
   rw⁻ 0 (q219 c4) ∷
   rw⁻ 1 (q230 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = eqn (CX42 ∷ Toff023 ∷ []) (Toff023 ∷ CX42 ∷ Toff034 ∷ []) (wp 267 c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (CCZ014 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ CCZ014 ∷ []) (wp 268 c4)
  q233 : Ws → Eqn
  q233 c4 = eqn (CCZ014 ∷ CX42 ∷ []) (CX42 ∷ CCZ014 ∷ []) (wp 269 c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl 310 (lit c4))
  q235 : Ws → Eqn
  q235 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl 222 (lit c4))
  q236 : Ws → Eqn
  q236 c4 = eqn (CX34 ∷ Toff023 ∷ []) (Toff023 ∷ CX34 ∷ []) (wp 270 c4)
  q237 : Ws → Eqn
  q237 c4 = eqn (CS14 ∷ Toff023 ∷ []) (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (Toff023 ∷ Toff034 ∷ []) (Toff034 ∷ Toff023 ∷ []) (wp 173 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (CX42 ∷ Toff034 ∷ Toff034 ∷ []) (CX42 ∷ []) (wp 271 c4)
  q240 : Ws → Eqn
  q240 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp 272 c4)
  q241 : Ws → Eqn
  q241 c4 = eqn (CCZ134 ∷ []) (CX42 ∷ CCZ134 ∷ CX42 ∷ []) (wl 312 (lit c4))

-- CXcb-box @133441: 18 steps
lem-CXcb-box-at133441 : Ws → ⟪ (CX42 ∷ Bx0-3241 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at133441 c4 = derive (CX42 ∷ Bx0-3241 ∷ CX42 ∷ []) (Bx0-3241 ∷ CCZ134 ∷ [])
  (rw 1 (q219 c4) ∷
   rw 0 (q231 c4) ∷
   rw⁻ 2 (q232 c4) ∷
   rw⁻ 1 (q233 c4) ∷
   rw 4 (q234 c4) ∷
   rw 8 (q235 c4) ∷
   rw 7 (q236 c4) ∷
   rw 6 (q37 c4) ∷
   rw 5 (q236 c4) ∷
   rw 4 (q237 c4) ∷
   rw⁻ 5 (q234 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw 2 (q231 c4) ∷
   rw 3 (q239 c4) ∷
   rw⁻ 4 (q240 c4) ∷
   rw⁻ 3 (q233 c4) ∷
   rw⁻ 0 (q219 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = eqn (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (lem-VPQ-at13243241 c4)

-- QVQ @13243241: 3 steps
lem-QVQ-at13243241 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at13243241 c4 = derive (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q163 c4) ∷
   rw⁻ 1 (q242 c4) ∷
   rw 4 (q165 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl 420 (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (lem-VPQ-at021021 c4)

-- QVQ @021021: 3 steps
lem-QVQ-at021021 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at021021 c4 = derive (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  (rw⁻ 0 (q243 c4) ∷
   rw⁻ 1 (q244 c4) ∷
   rw 4 (q115 c4) ∷ []) Eq.refl

private
  q245 : Ws → Eqn
  q245 c4 = eqn (CX14 ∷ Toff013 ∷ []) (Toff013 ∷ CX14 ∷ []) (wp 281 c4)
  q246 : Ws → Eqn
  q246 c4 = eqn (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (CX14 ∷ CCZ024 ∷ []) (wp 282 c4)
  q247 : Ws → Eqn
  q247 c4 = eqn (CCZ012 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl 422 (lit c4))
  q248 : Ws → Eqn
  q248 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl 297 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp 92 c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4))
  q251 : Ws → Eqn
  q251 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp 87 c4)
  q252 : Ws → Eqn
  q252 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) (wp 142 c4)
  q254 : Ws → Eqn
  q254 c4 = eqn (CX14 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX14 ∷ []) (wp 283 c4)

-- CXbc-box @13213442: 17 steps
lem-CXbc-box-at13213442 : Ws → ⟪ (CX14 ∷ Bx0-3142 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at13213442 c4 = derive (CX14 ∷ Bx0-3142 ∷ CX14 ∷ []) (Bx0-3142 ∷ CCZ123 ∷ [])
  (rw 1 (q166 c4) ∷
   rw 0 (q245 c4) ∷
   rw⁻ 1 (q246 c4) ∷
   rw 3 (q247 c4) ∷
   rw 2 (q245 c4) ∷
   rw 5 (q248 c4) ∷
   rw⁻ 9 (q249 c4) ∷
   rw 8 (q250 c4) ∷
   rw⁻ 7 (q251 c4) ∷
   rw 6 (q250 c4) ∷
   rw⁻ 5 (q252 c4) ∷
   rw⁻ 6 (q248 c4) ∷
   rw 4 (q253 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw 4 (q254 c4) ∷
   rw⁻ 0 (q166 c4) ∷
   rw⁻ 1 (q155 c4) ∷ []) Eq.refl

private
  q255 : Ws → Eqn
  q255 c4 = eqn (CX41 ∷ Toff013 ∷ []) (Toff013 ∷ CX41 ∷ Toff034 ∷ []) (wp 284 c4)
  q256 : Ws → Eqn
  q256 c4 = eqn (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ024 ∷ []) (wp 96 c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (CCZ024 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ []) (wp 285 c4)
  q258 : Ws → Eqn
  q258 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl 293 (lit c4))
  q259 : Ws → Eqn
  q259 c4 = eqn (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) (wl 246 (lit c4))
  q260 : Ws → Eqn
  q260 c4 = eqn (CX34 ∷ Toff013 ∷ []) (Toff013 ∷ CX34 ∷ []) (wp 286 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (CS24 ∷ Toff013 ∷ []) (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) (wp 97 c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (CX41 ∷ Toff034 ∷ Toff034 ∷ []) (CX41 ∷ []) (wp 287 c4)
  q264 : Ws → Eqn
  q264 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)

-- CXcb-box @13213442: 18 steps
lem-CXcb-box-at13213442 : Ws → ⟪ (CX41 ∷ Bx0-3142 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at13213442 c4 = derive (CX41 ∷ Bx0-3142 ∷ CX41 ∷ []) (Bx0-3142 ∷ CCZ234 ∷ [])
  (rw 1 (q166 c4) ∷
   rw 0 (q255 c4) ∷
   rw⁻ 2 (q256 c4) ∷
   rw⁻ 1 (q257 c4) ∷
   rw 4 (q258 c4) ∷
   rw 8 (q259 c4) ∷
   rw 7 (q260 c4) ∷
   rw 6 (q50 c4) ∷
   rw 5 (q260 c4) ∷
   rw 4 (q261 c4) ∷
   rw⁻ 5 (q258 c4) ∷
   rw⁻ 3 (q262 c4) ∷
   rw 2 (q255 c4) ∷
   rw 3 (q263 c4) ∷
   rw⁻ 4 (q264 c4) ∷
   rw⁻ 3 (q257 c4) ∷
   rw⁻ 0 (q166 c4) ∷
   rw⁻ 1 (q144 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = eqn (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (lem-VPQ-at13243142 c4)

-- QVQ @13243142: 3 steps
lem-QVQ-at13243142 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at13243142 c4 = derive (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q163 c4) ∷
   rw⁻ 1 (q265 c4) ∷
   rw 4 (q165 c4) ∷ []) Eq.refl

private
  q266 : Ws → Eqn
  q266 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl 442 (lit c4))
  q267 : Ws → Eqn
  q267 c4 = eqn (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (lem-VPQ-at03102132 c4)

-- QVQ @03102132: 3 steps
lem-QVQ-at03102132 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at03102132 c4 = derive (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  (rw⁻ 0 (q266 c4) ∷
   rw⁻ 1 (q267 c4) ∷
   rw 4 (q115 c4) ∷ []) Eq.refl

private
  q268 : Ws → Eqn
  q268 c4 = eqn (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4)
  q269 : Ws → Eqn
  q269 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP-at3443 c4)

-- P-box @3443: 8 steps
lem-P-box-at3443 : Ws → ⟪ (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-P-box-at3443 c4 = derive (Toff034 ∷ Bx0-1243 ∷ Toff034 ∷ []) (Bx0-1243 ∷ [])
  (rw 1 (q268 c4) ∷
   rw⁻ 0 (q269 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 3 (q269 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 0 (q268 c4) ∷ []) Eq.refl

-- VPQ @3443: 14 steps
lem-VPQ-at3443 : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at3443 c4 = derive (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q269 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = eqn (Toff423 ∷ Toff423 ∷ []) [] (wl 457 (lit c4))
  q271 : Ws → Eqn
  q271 c4 = eqn (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (lem-VPQ-at0410213243 c4)

-- QVQ @0410213243: 3 steps
lem-QVQ-at0410213243 : Ws → ⟪ (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-QVQ-at0410213243 c4 = derive (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ [])
  (rw⁻ 0 (q270 c4) ∷
   rw⁻ 1 (q271 c4) ∷
   rw 4 (q115 c4) ∷ []) Eq.refl

private
  q272 : Ws → Eqn
  q272 c4 = eqn (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ []) (wl 468 (lit c4))
  q273 : Ws → Eqn
  q273 c4 = eqn (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ []) (wp 316 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (CS03⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))
  q275 : Ws → Eqn
  q275 c4 = eqn (Toff412 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 (lit c4))
  q276 : Ws → Eqn
  q276 c4 = eqn (CS03⁻ ∷ S4 ∷ []) (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))
  q277 : Ws → Eqn
  q277 c4 = eqn (CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03⁻ ∷ []) (wl 469 (lit c4))
  q278 : Ws → Eqn
  q278 c4 = eqn (S4⁻ ∷ S4 ∷ []) [] (wl 456 (lit c4))
  q279 : Ws → Eqn
  q279 c4 = eqn (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (CS12⁻ ∷ S4 ∷ []) (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑))
  q281 : Ws → Eqn
  q281 c4 = eqn (CS12⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4))
  q282 : Ws → Eqn
  q282 c4 = eqn (CS12⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))

-- VPQ @043043: 14 steps
lem-VPQ-at043043 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at043043 c4 = derive (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q272 c4) ∷
   rw⁻ 4 (q273 c4) ∷
   rw⁻ 3 (q274 c4) ∷
   rw 2 (q275 c4) ∷
   rw⁻ 1 (q276 c4) ∷
   rw⁻ 0 (q277 c4) ∷
   rw 4 (q278 c4) ∷
   rw 3 (q279 c4) ∷
   rw⁻ 4 (q278 c4) ∷
   rw 1 (q280 c4) ∷
   rw 2 (q281 c4) ∷
   rw 3 (q282 c4) ∷
   rw 0 (q273 c4) ∷
   rw 2 (q272 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = eqn (Bx4-1203 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (CX20 ∷ Toff412 ∷ []) (Toff412 ∷ CX20 ∷ []) (wp 330 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (CCZ234 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl 475 (lit c4))
  q286 : Ws → Eqn
  q286 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl 207 (lit c4))
  q287 : Ws → Eqn
  q287 c4 = eqn (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) (wp 312 c4)
  q288 : Ws → Eqn
  q288 c4 = eqn (CCZ034 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ034 ∷ []) (wp 313 c4)
  q289 : Ws → Eqn
  q289 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp 314 c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (CCZ123 ∷ []) (CX20 ∷ CCZ123 ∷ CX20 ∷ []) (wl 476 (lit c4))

-- CXbc-box @043043: 17 steps
lem-CXbc-box-at043043 : Ws → ⟪ (CX20 ∷ Bx4-1203 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at043043 c4 = derive (CX20 ∷ Bx4-1203 ∷ CX20 ∷ []) (Bx4-1203 ∷ CCZ123 ∷ [])
  (rw 1 (q283 c4) ∷
   rw 0 (q284 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 3 (q285 c4) ∷
   rw 2 (q284 c4) ∷
   rw 5 (q286 c4) ∷
   rw⁻ 9 (q287 c4) ∷
   rw 8 (q72 c4) ∷
   rw⁻ 7 (q288 c4) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 5 (q289 c4) ∷
   rw⁻ 6 (q286 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   rw⁻ 0 (q283 c4) ∷
   rw⁻ 1 (q290 c4) ∷ []) Eq.refl

private
  q291 : Ws → Eqn
  q291 c4 = eqn (CX02 ∷ Toff412 ∷ []) (Toff412 ∷ CX02 ∷ Toff401 ∷ []) (wp 331 c4)
  q292 : Ws → Eqn
  q292 c4 = eqn (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (Toff401 ∷ CCZ034 ∷ []) (wp 332 c4)
  q293 : Ws → Eqn
  q293 c4 = eqn (CCZ034 ∷ CX02 ∷ []) (CX02 ∷ CCZ034 ∷ []) (wp 333 c4)
  q294 : Ws → Eqn
  q294 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl 477 (lit c4))
  q295 : Ws → Eqn
  q295 c4 = eqn (CS13 ∷ Toff412 ∷ []) (Toff412 ∷ CS13 ∷ []) (wl 478 (lit c4))
  q296 : Ws → Eqn
  q296 c4 = eqn (CX10 ∷ Toff412 ∷ []) (Toff412 ∷ CX10 ∷ []) (wp 334 c4)
  q297 : Ws → Eqn
  q297 c4 = eqn (CS03⁻ ∷ Toff412 ∷ []) (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4))
  q298 : Ws → Eqn
  q298 c4 = eqn (CS03 ∷ Toff412 ∷ []) (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4))
  q299 : Ws → Eqn
  q299 c4 = eqn (Toff401 ∷ Toff412 ∷ []) (Toff412 ∷ Toff401 ∷ []) (wp 335 c4)
  q300 : Ws → Eqn
  q300 c4 = eqn (CX02 ∷ Toff401 ∷ Toff401 ∷ []) (CX02 ∷ []) (wp 336 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (CCZ013 ∷ []) (CX02 ∷ CCZ013 ∷ CX02 ∷ []) (wl 479 (lit c4))

-- CXcb-box @043043: 18 steps
lem-CXcb-box-at043043 : Ws → ⟪ (CX02 ∷ Bx4-1203 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at043043 c4 = derive (CX02 ∷ Bx4-1203 ∷ CX02 ∷ []) (Bx4-1203 ∷ CCZ013 ∷ [])
  (rw 1 (q283 c4) ∷
   rw 0 (q291 c4) ∷
   rw⁻ 2 (q292 c4) ∷
   rw⁻ 1 (q293 c4) ∷
   rw 4 (q294 c4) ∷
   rw 8 (q295 c4) ∷
   rw 7 (q296 c4) ∷
   rw 6 (q297 c4) ∷
   rw 5 (q296 c4) ∷
   rw 4 (q298 c4) ∷
   rw⁻ 5 (q294 c4) ∷
   rw 3 (q299 c4) ∷
   rw 2 (q291 c4) ∷
   rw 3 (q300 c4) ∷
   rw 4 (q142 c4) ∷
   rw⁻ 3 (q293 c4) ∷
   rw⁻ 0 (q283 c4) ∷
   rw⁻ 1 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = eqn (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (lem-VPQ-at04203243 c4)

-- QVQ @04203243: 3 steps
lem-QVQ-at04203243 : Ws → ⟪ (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-QVQ-at04203243 c4 = derive (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ [])
  (rw⁻ 0 (q270 c4) ∷
   rw⁻ 1 (q302 c4) ∷
   rw 4 (q115 c4) ∷ []) Eq.refl

private
  q303 : Ws → Eqn
  q303 c4 = eqn (Bx3-1204 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0330 c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ []) (lem-tP-at0330 c4)
  q305 : Ws → Eqn
  q305 c4 = eqn (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ []) (wp 344 c4)
  q306 : Ws → Eqn
  q306 c4 = eqn (CCZ034 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff304 ∷ []) (wp 345 c4)
  q307 : Ws → Eqn
  q307 c4 = eqn (CZ04 ∷ Toff312 ∷ []) (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4))
  q308 : Ws → Eqn
  q308 c4 = eqn (CCZ034 ∷ []) (CZ04 ∷ CCZ034 ∷ CZ04 ∷ []) (wp 346 c4)

-- P-box @0330: 8 steps
lem-P-box-at0330 : Ws → ⟪ (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-P-box-at0330 c4 = derive (Toff304 ∷ Bx3-1204 ∷ Toff304 ∷ []) (Bx3-1204 ∷ [])
  (rw 1 (q303 c4) ∷
   rw⁻ 0 (q304 c4) ∷
   rw⁻ 1 (q305 c4) ∷
   rw⁻ 3 (q304 c4) ∷
   rw⁻ 4 (q306 c4) ∷
   rw 2 (q307 c4) ∷
   rw⁻ 3 (q308 c4) ∷
   rw⁻ 0 (q303 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = eqn (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ []) (wl 488 (lit c4))
  q310 : Ws → Eqn
  q310 c4 = eqn (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ []) (wp 347 c4)
  q311 : Ws → Eqn
  q311 c4 = eqn (CS04⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS04⁻ ∷ []) (wp 348 c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (Toff312 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff312 ∷ []) (lem-comm-TOFF312-CSd04 (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (CS04⁻ ∷ S3 ∷ []) (S3 ∷ CS04⁻ ∷ []) (wp 349 c4)
  q314 : Ws → Eqn
  q314 c4 = eqn (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ []) (wp 350 c4)
  q315 : Ws → Eqn
  q315 c4 = eqn (S3⁻ ∷ S3 ∷ []) [] (wl 441 (lit c4))
  q316 : Ws → Eqn
  q316 c4 = eqn (CS12⁻ ∷ S3 ∷ []) (S3 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S))
  q317 : Ws → Eqn
  q317 c4 = eqn (CS12⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4))
  q318 : Ws → Eqn
  q318 c4 = eqn (CS12⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S • S • S))

-- VPQ @0330: 14 steps
lem-VPQ-at0330 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at0330 c4 = derive (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q309 c4) ∷
   rw⁻ 4 (q310 c4) ∷
   rw⁻ 3 (q311 c4) ∷
   rw 2 (q312 c4) ∷
   rw⁻ 1 (q313 c4) ∷
   rw⁻ 0 (q314 c4) ∷
   rw 4 (q315 c4) ∷
   rw 3 (q304 c4) ∷
   rw⁻ 4 (q315 c4) ∷
   rw 1 (q316 c4) ∷
   rw 2 (q317 c4) ∷
   rw 3 (q318 c4) ∷
   rw 0 (q310 c4) ∷
   rw 2 (q309 c4) ∷ []) Eq.refl

private
  q319 : Ws → Eqn
  q319 c4 = eqn (Toff304 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4))
  q320 : Ws → Eqn
  q320 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203142 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (CS04⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4))

-- VPQ @0314203142: 14 steps
lem-VPQ-at0314203142 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0314203142 c4 = derive (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q310 c4) ∷
   rw⁻ 4 (q309 c4) ∷
   rw⁻ 3 (q318 c4) ∷
   rw 2 (q319 c4) ∷
   rw⁻ 1 (q316 c4) ∷
   rw 0 (q314 c4) ∷
   rw 4 (q315 c4) ∷
   rw 3 (q320 c4) ∷
   rw⁻ 4 (q315 c4) ∷
   rw 1 (q313 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q311 c4) ∷
   rw 0 (q309 c4) ∷
   rw 2 (q310 c4) ∷ []) Eq.refl

private
  q322 : Ws → Eqn
  q322 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4)
  q323 : Ws → Eqn
  q323 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4)
  q324 : Ws → Eqn
  q324 c4 = eqn (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ []) (wl 504 (lit c4))
  q325 : Ws → Eqn
  q325 c4 = eqn (CCZ123 ∷ CZ12 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff312 ∷ []) (wl 505 (lit c4))
  q326 : Ws → Eqn
  q326 c4 = eqn (CZ12 ∷ Toff304 ∷ []) (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4))
  q327 : Ws → Eqn
  q327 c4 = eqn (CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ CZ12 ∷ []) (wl 506 (lit c4))

-- P-box @0310243142: 8 steps
lem-P-box-at0310243142 : Ws → ⟪ (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-P-box-at0310243142 c4 = derive (Toff312 ∷ Bx3-0412 ∷ Toff312 ∷ []) (Bx3-0412 ∷ [])
  (rw 1 (q322 c4) ∷
   rw⁻ 0 (q323 c4) ∷
   rw⁻ 1 (q324 c4) ∷
   rw⁻ 3 (q323 c4) ∷
   rw⁻ 4 (q325 c4) ∷
   rw 2 (q326 c4) ∷
   rw⁻ 3 (q327 c4) ∷
   rw⁻ 0 (q322 c4) ∷ []) Eq.refl

-- VPQ @0310243142: 14 steps
lem-VPQ-at0310243142 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0310243142 c4 = derive (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q310 c4) ∷
   rw⁻ 4 (q309 c4) ∷
   rw⁻ 3 (q318 c4) ∷
   rw 2 (q319 c4) ∷
   rw⁻ 1 (q316 c4) ∷
   rw 0 (q314 c4) ∷
   rw 4 (q315 c4) ∷
   rw 3 (q323 c4) ∷
   rw⁻ 4 (q315 c4) ∷
   rw 1 (q313 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q311 c4) ∷
   rw 0 (q309 c4) ∷
   rw 2 (q310 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = eqn (CX02 ∷ CX20 ∷ CX02 ∷ []) (Sw02 ∷ []) (wl 509 (lit c4))
  q329 : Ws → Eqn
  q329 c4 = eqn (CX02 ∷ Bx4-1023 ∷ CX02 ∷ []) (Bx4-1023 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04203243 c4)
  q330 : Ws → Eqn
  q330 c4 = eqn (CCZ013 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl 483 (lit c4))
  q331 : Ws → Eqn
  q331 c4 = eqn (CX20 ∷ Bx4-1023 ∷ CX20 ∷ []) (Bx4-1023 ∷ CCZ123 ∷ []) (lem-CXcb-box-at04203243 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (CCZ013 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ []) (wl 444 (lit c4))
  q333 : Ws → Eqn
  q333 c4 = eqn (CCZ123 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl 481 (lit c4))
  q334 : Ws → Eqn
  q334 c4 = eqn (CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) (wl 510 (lit c4))
  q335 : Ws → Eqn
  q335 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))

-- SWbc-box @04203243: 11 steps
lem-SWbc-box-at04203243 : Ws → ⟪ (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-SWbc-box-at04203243 c4 = derive (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (Bx4-1023 ∷ [])
  (rw⁻ 0 (q328 c4) ∷
   rw⁻ 4 (q328 c4) ∷
   rw 2 (q329 c4) ∷
   rw 3 (q330 c4) ∷
   rw 1 (q331 c4) ∷
   rw 4 (q332 c4) ∷
   rw 3 (q333 c4) ∷
   rw 2 (q333 c4) ∷
   rw 3 (q334 c4) ∷
   rw 0 (q329 c4) ∷
   rw 1 (q335 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = eqn (CX02 ∷ Bx3-1024 ∷ CX02 ∷ []) (Bx3-1024 ∷ CCZ014 ∷ []) (lem-CXbc-box-at032032 c4)
  q337 : Ws → Eqn
  q337 c4 = eqn (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 381 c4)
  q338 : Ws → Eqn
  q338 c4 = eqn (CX20 ∷ Bx3-1024 ∷ CX20 ∷ []) (Bx3-1024 ∷ CCZ124 ∷ []) (lem-CXcb-box-at032032 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (CCZ014 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ []) (wp 308 c4)
  q340 : Ws → Eqn
  q340 c4 = eqn (CCZ124 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp 382 c4)
  q341 : Ws → Eqn
  q341 c4 = eqn (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp 383 c4)
  q342 : Ws → Eqn
  q342 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)

-- SWbc-box @032032: 11 steps
lem-SWbc-box-at032032 : Ws → ⟪ (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-SWbc-box-at032032 c4 = derive (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (Bx3-1024 ∷ [])
  (rw⁻ 0 (q328 c4) ∷
   rw⁻ 4 (q328 c4) ∷
   rw 2 (q336 c4) ∷
   rw 3 (q337 c4) ∷
   rw 1 (q338 c4) ∷
   rw 4 (q339 c4) ∷
   rw 3 (q340 c4) ∷
   rw 2 (q340 c4) ∷
   rw 3 (q341 c4) ∷
   rw 0 (q336 c4) ∷
   rw 1 (q342 c4) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = eqn (CCZ124 ∷ Toff412 ∷ CZ12 ∷ []) (Toff412 ∷ CCZ124 ∷ []) (wl 532 (lit c4))
  q344 : Ws → Eqn
  q344 c4 = eqn (CZ12 ∷ Toff403 ∷ []) (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4))
  q345 : Ws → Eqn
  q345 c4 = eqn (CCZ124 ∷ Toff412 ∷ []) (Toff412 ∷ CZ12 ∷ CCZ124 ∷ []) (wl 533 (lit c4))

-- t-cP @043043: 5 steps
lem-t-cP-at043043 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-t-cP-at043043 c4 = derive (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q343 c4) ∷
   rw 2 (q344 c4) ∷
   rw 1 (q279 c4) ∷
   rw⁻ 2 (q345 c4) ∷
   rw 3 (q279 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = eqn (CX20 ∷ Toff312 ∷ []) (Toff312 ∷ CX20 ∷ []) (wl 534 (lit c4))
  q347 : Ws → Eqn
  q347 c4 = eqn (CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl 535 (lit c4))
  q348 : Ws → Eqn
  q348 c4 = eqn (CCZ124 ∷ []) (CX20 ∷ CCZ124 ∷ CX20 ∷ []) (wp 380 c4)

-- CXbc-box @0330: 17 steps
lem-CXbc-box-at0330 : Ws → ⟪ (CX20 ∷ Bx3-1204 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at0330 c4 = derive (CX20 ∷ Bx3-1204 ∷ CX20 ∷ []) (Bx3-1204 ∷ CCZ124 ∷ [])
  (rw 1 (q303 c4) ∷
   rw 0 (q346 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 3 (q347 c4) ∷
   rw 2 (q346 c4) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 8 (q72 c4) ∷
   rw⁻ 7 (q73 c4) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 5 (q74 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   rw⁻ 0 (q303 c4) ∷
   rw⁻ 1 (q348 c4) ∷ []) Eq.refl

private
  q349 : Ws → Eqn
  q349 c4 = eqn (CX02 ∷ Toff312 ∷ []) (Toff312 ∷ CX02 ∷ Toff301 ∷ []) (wl 536 (lit c4))
  q350 : Ws → Eqn
  q350 c4 = eqn (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ []) (wp 388 c4)
  q351 : Ws → Eqn
  q351 c4 = eqn (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp 341 c4)
  q352 : Ws → Eqn
  q352 c4 = eqn (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) (wl 499 (lit c4))
  q353 : Ws → Eqn
  q353 c4 = eqn (CX10 ∷ Toff312 ∷ []) (Toff312 ∷ CX10 ∷ []) (wl 537 (lit c4))
  q354 : Ws → Eqn
  q354 c4 = eqn (CS04 ∷ Toff312 ∷ []) (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4))
  q355 : Ws → Eqn
  q355 c4 = eqn (Toff301 ∷ Toff312 ∷ []) (Toff312 ∷ Toff301 ∷ []) (wl 525 (lit c4))
  q356 : Ws → Eqn
  q356 c4 = eqn (CX02 ∷ Toff301 ∷ Toff301 ∷ []) (CX02 ∷ []) (wl 538 (lit c4))
  q357 : Ws → Eqn
  q357 c4 = eqn (CCZ014 ∷ []) (CX02 ∷ CCZ014 ∷ CX02 ∷ []) (wp 378 c4)

-- CXcb-box @0330: 18 steps
lem-CXcb-box-at0330 : Ws → ⟪ (CX02 ∷ Bx3-1204 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0330 c4 = derive (CX02 ∷ Bx3-1204 ∷ CX02 ∷ []) (Bx3-1204 ∷ CCZ014 ∷ [])
  (rw 1 (q303 c4) ∷
   rw 0 (q349 c4) ∷
   rw⁻ 2 (q350 c4) ∷
   rw⁻ 1 (q293 c4) ∷
   rw 4 (q351 c4) ∷
   rw 8 (q352 c4) ∷
   rw 7 (q353 c4) ∷
   rw 6 (q321 c4) ∷
   rw 5 (q353 c4) ∷
   rw 4 (q354 c4) ∷
   rw⁻ 5 (q351 c4) ∷
   rw 3 (q355 c4) ∷
   rw 2 (q349 c4) ∷
   rw 3 (q356 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 3 (q293 c4) ∷
   rw⁻ 0 (q303 c4) ∷
   rw⁻ 1 (q357 c4) ∷ []) Eq.refl

private
  q358 : Ws → Eqn
  q358 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4)
  q359 : Ws → Eqn
  q359 c4 = eqn (CS04⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) (wp 422 c4)
  q360 : Ws → Eqn
  q360 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp 301 c4)
  q361 : Ws → Eqn
  q361 c4 = eqn (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ []) (wp 48 c4)
  q362 : Ws → Eqn
  q362 c4 = eqn (CCZ023 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ []) (wl 560 (lit c4))
  q363 : Ws → Eqn
  q363 c4 = eqn (CS14⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4))
  q364 : Ws → Eqn
  q364 c4 = eqn (CS14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4))
  q365 : Ws → Eqn
  q365 c4 = eqn (CCZ023 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ023 ∷ []) (wp 47 c4)
  q366 : Ws → Eqn
  q366 c4 = eqn (CS14⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS14⁻ ∷ []) (wp 423 c4)
  q367 : Ws → Eqn
  q367 c4 = eqn (CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ CS14⁻ ∷ CZ14 ∷ CCZ014 ∷ []) (CS04⁻ ∷ []) (wp 424 c4)

-- CSdu-box-2 @243243: 17 steps
lem-CSdu-box-2-at243243 : Ws → ⟪ (CS04⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at243243 c4 = derive (CS04⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ [])
  (rw 1 (q358 c4) ∷
   rw 0 (q359 c4) ∷
   rw 3 (q360 c4) ∷
   rw⁻ 7 (q361 c4) ∷
   rw⁻ 6 (q362 c4) ∷
   rw 5 (q363 c4) ∷
   rw⁻ 4 (q362 c4) ∷
   rw 3 (q364 c4) ∷
   rw⁻ 4 (q360 c4) ∷
   rw 2 (q363 c4) ∷
   rw⁻ 1 (q365 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q366 c4) ∷
   rw 2 (q359 c4) ∷
   rw 3 (q367 c4) ∷
   rw⁻ 3 (q365 c4) ∷
   rw⁻ 0 (q358 c4) ∷ []) Eq.refl

private
  q368 : Ws → Eqn
  q368 c4 = eqn (S0 ∷ Toff014 ∷ []) (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) (wp 425 c4)
  q369 : Ws → Eqn
  q369 c4 = eqn (CCZ023 ∷ S0 ∷ []) (S0 ∷ CCZ023 ∷ []) (wl 561 (lit c4))
  q370 : Ws → Eqn
  q370 c4 = eqn (CS14 ∷ Toff014 ∷ []) (Toff014 ∷ CS14 ∷ []) (wp 426 c4)
  q371 : Ws → Eqn
  q371 c4 = eqn (S0 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (S0 ∷ []) (wp 427 c4)

-- Su-box @243243: 17 steps
lem-Su-box-at243243 : Ws → ⟪ (S0 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box-at243243 c4 = derive (S0 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ S0 ∷ [])
  (rw 1 (q358 c4) ∷
   rw 0 (q368 c4) ∷
   rw 3 (q360 c4) ∷
   rw⁻ 7 (q361 c4) ∷
   rw⁻ 6 (q362 c4) ∷
   rw 5 (q363 c4) ∷
   rw⁻ 4 (q362 c4) ∷
   rw 3 (q364 c4) ∷
   rw⁻ 4 (q360 c4) ∷
   rw 2 (q364 c4) ∷
   rw⁻ 1 (q369 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q370 c4) ∷
   rw 2 (q368 c4) ∷
   rw 3 (q371 c4) ∷
   rw⁻ 3 (q369 c4) ∷
   rw⁻ 0 (q358 c4) ∷ []) Eq.refl

private
  q372 : Ws → Eqn
  q372 c4 = eqn (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4)
  q373 : Ws → Eqn
  q373 c4 = eqn (CS04⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) (wp 431 c4)
  q374 : Ws → Eqn
  q374 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp 296 c4)
  q375 : Ws → Eqn
  q375 c4 = eqn (CCZ013 ∷ CS04 ∷ []) (CS04 ∷ CCZ013 ∷ []) (wp 77 c4)
  q376 : Ws → Eqn
  q376 c4 = eqn (CS24⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4))
  q377 : Ws → Eqn
  q377 c4 = eqn (CS24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4))
  q378 : Ws → Eqn
  q378 c4 = eqn (CCZ013 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ013 ∷ []) (wp 76 c4)
  q379 : Ws → Eqn
  q379 c4 = eqn (CS24⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS24⁻ ∷ []) (wp 432 c4)
  q380 : Ws → Eqn
  q380 c4 = eqn (CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ CS24⁻ ∷ CZ24 ∷ CCZ024 ∷ []) (CS04⁻ ∷ []) (wp 433 c4)

-- CSdu-box-2 @122441: 17 steps
lem-CSdu-box-2-at122441 : Ws → ⟪ (CS04⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at122441 c4 = derive (CS04⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04⁻ ∷ [])
  (rw 1 (q372 c4) ∷
   rw 0 (q373 c4) ∷
   rw 3 (q374 c4) ∷
   rw⁻ 7 (q375 c4) ∷
   rw⁻ 6 (q332 c4) ∷
   rw 5 (q376 c4) ∷
   rw⁻ 4 (q332 c4) ∷
   rw 3 (q377 c4) ∷
   rw⁻ 4 (q374 c4) ∷
   rw 2 (q376 c4) ∷
   rw⁻ 1 (q378 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q379 c4) ∷
   rw 2 (q373 c4) ∷
   rw 3 (q380 c4) ∷
   rw⁻ 3 (q378 c4) ∷
   rw⁻ 0 (q372 c4) ∷ []) Eq.refl

private
  q381 : Ws → Eqn
  q381 c4 = eqn (S0 ∷ Toff024 ∷ []) (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) (wp 434 c4)
  q382 : Ws → Eqn
  q382 c4 = eqn (CCZ013 ∷ S0 ∷ []) (S0 ∷ CCZ013 ∷ []) (wl 562 (lit c4))
  q383 : Ws → Eqn
  q383 c4 = eqn (CS24 ∷ Toff024 ∷ []) (Toff024 ∷ CS24 ∷ []) (wp 435 c4)
  q384 : Ws → Eqn
  q384 c4 = eqn (S0 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (S0 ∷ []) (wp 436 c4)

-- Su-box @122441: 17 steps
lem-Su-box-at122441 : Ws → ⟪ (S0 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box-at122441 c4 = derive (S0 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ S0 ∷ [])
  (rw 1 (q372 c4) ∷
   rw 0 (q381 c4) ∷
   rw 3 (q374 c4) ∷
   rw⁻ 7 (q375 c4) ∷
   rw⁻ 6 (q332 c4) ∷
   rw 5 (q376 c4) ∷
   rw⁻ 4 (q332 c4) ∷
   rw 3 (q377 c4) ∷
   rw⁻ 4 (q374 c4) ∷
   rw 2 (q377 c4) ∷
   rw⁻ 1 (q382 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q383 c4) ∷
   rw 2 (q381 c4) ∷
   rw 3 (q384 c4) ∷
   rw⁻ 3 (q382 c4) ∷
   rw⁻ 0 (q372 c4) ∷ []) Eq.refl

private
  q385 : Ws → Eqn
  q385 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4)
  q386 : Ws → Eqn
  q386 c4 = eqn (CS24⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp 449 c4)
  q387 : Ws → Eqn
  q387 c4 = eqn (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp 450 c4)
  q388 : Ws → Eqn
  q388 c4 = eqn (CCZ123 ∷ CS24 ∷ []) (CS24 ∷ CCZ123 ∷ []) (wl 173 (lit c4))
  q389 : Ws → Eqn
  q389 c4 = eqn (CCZ123 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ []) (wl 482 (lit c4))
  q390 : Ws → Eqn
  q390 c4 = eqn (CS04⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4))
  q391 : Ws → Eqn
  q391 c4 = eqn (CS04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4))
  q392 : Ws → Eqn
  q392 c4 = eqn (CCZ123 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ123 ∷ []) (wl 172 (lit c4))
  q393 : Ws → Eqn
  q393 c4 = eqn (CS04⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS04⁻ ∷ []) (wp 451 c4)
  q394 : Ws → Eqn
  q394 c4 = eqn (CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) (CS24⁻ ∷ []) (wp 452 c4)

-- CSdu-box-2 @0210243143: 17 steps
lem-CSdu-box-2-at0210243143 : Ws → ⟪ (CS24⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at0210243143 c4 = derive (CS24⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24⁻ ∷ [])
  (rw 1 (q385 c4) ∷
   rw 0 (q386 c4) ∷
   rw 3 (q387 c4) ∷
   rw⁻ 7 (q388 c4) ∷
   rw⁻ 6 (q389 c4) ∷
   rw 5 (q390 c4) ∷
   rw⁻ 4 (q389 c4) ∷
   rw 3 (q391 c4) ∷
   rw⁻ 4 (q387 c4) ∷
   rw 2 (q390 c4) ∷
   rw⁻ 1 (q392 c4) ∷
   rw 4 (q28 c4) ∷
   rw 3 (q393 c4) ∷
   rw 2 (q386 c4) ∷
   rw 3 (q394 c4) ∷
   rw⁻ 3 (q392 c4) ∷
   rw⁻ 0 (q385 c4) ∷ []) Eq.refl

private
  q395 : Ws → Eqn
  q395 c4 = eqn (S2 ∷ Toff204 ∷ []) (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ []) (wp 453 c4)
  q396 : Ws → Eqn
  q396 c4 = eqn (CCZ123 ∷ S2 ∷ []) (S2 ∷ CCZ123 ∷ []) (wl 582 (lit c4))
  q397 : Ws → Eqn
  q397 c4 = eqn (CS04 ∷ Toff204 ∷ []) (Toff204 ∷ CS04 ∷ []) (wp 454 c4)
  q398 : Ws → Eqn
  q398 c4 = eqn (S2 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (S2 ∷ []) (wp 455 c4)

-- Su-box @0210243143: 17 steps
lem-Su-box-at0210243143 : Ws → ⟪ (S2 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S2 ∷ []) ⟫ʷ
lem-Su-box-at0210243143 c4 = derive (S2 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S2 ∷ [])
  (rw 1 (q385 c4) ∷
   rw 0 (q395 c4) ∷
   rw 3 (q387 c4) ∷
   rw⁻ 7 (q388 c4) ∷
   rw⁻ 6 (q389 c4) ∷
   rw 5 (q390 c4) ∷
   rw⁻ 4 (q389 c4) ∷
   rw 3 (q391 c4) ∷
   rw⁻ 4 (q387 c4) ∷
   rw 2 (q391 c4) ∷
   rw⁻ 1 (q396 c4) ∷
   rw 4 (q28 c4) ∷
   rw 3 (q397 c4) ∷
   rw 2 (q395 c4) ∷
   rw 3 (q398 c4) ∷
   rw⁻ 3 (q396 c4) ∷
   rw⁻ 0 (q385 c4) ∷ []) Eq.refl

private
  q399 : Ws → Eqn
  q399 c4 = eqn (CS04 ∷ Toff014 ∷ []) (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) (wp 480 c4)
  q400 : Ws → Eqn
  q400 c4 = eqn (CS04 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (CS04 ∷ []) (wp 481 c4)

-- CSu-box-2 @243243: 17 steps
lem-CSu-box-2-at243243 : Ws → ⟪ (CS04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-2-at243243 c4 = derive (CS04 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS04 ∷ [])
  (rw 1 (q358 c4) ∷
   rw 0 (q399 c4) ∷
   rw 3 (q360 c4) ∷
   rw⁻ 7 (q361 c4) ∷
   rw⁻ 6 (q362 c4) ∷
   rw 5 (q363 c4) ∷
   rw⁻ 4 (q362 c4) ∷
   rw 3 (q364 c4) ∷
   rw⁻ 4 (q360 c4) ∷
   rw 2 (q364 c4) ∷
   rw⁻ 1 (q361 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q370 c4) ∷
   rw 2 (q399 c4) ∷
   rw 3 (q400 c4) ∷
   rw⁻ 3 (q361 c4) ∷
   rw⁻ 0 (q358 c4) ∷ []) Eq.refl

private
  q401 : Ws → Eqn
  q401 c4 = eqn (CS04 ∷ Toff024 ∷ []) (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) (wp 487 c4)
  q402 : Ws → Eqn
  q402 c4 = eqn (CS04 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (CS04 ∷ []) (wp 488 c4)

-- CSu-box-2 @122441: 17 steps
lem-CSu-box-2-at122441 : Ws → ⟪ (CS04 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-2-at122441 c4 = derive (CS04 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS04 ∷ [])
  (rw 1 (q372 c4) ∷
   rw 0 (q401 c4) ∷
   rw 3 (q374 c4) ∷
   rw⁻ 7 (q375 c4) ∷
   rw⁻ 6 (q332 c4) ∷
   rw 5 (q376 c4) ∷
   rw⁻ 4 (q332 c4) ∷
   rw 3 (q377 c4) ∷
   rw⁻ 4 (q374 c4) ∷
   rw 2 (q377 c4) ∷
   rw⁻ 1 (q375 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q383 c4) ∷
   rw 2 (q401 c4) ∷
   rw 3 (q402 c4) ∷
   rw⁻ 3 (q375 c4) ∷
   rw⁻ 0 (q372 c4) ∷ []) Eq.refl

private
  q403 : Ws → Eqn
  q403 c4 = eqn (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4)
  q404 : Ws → Eqn
  q404 c4 = eqn (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ []) (wp 497 c4)
  q405 : Ws → Eqn
  q405 c4 = eqn (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (CX01 ∷ CCZ123 ∷ []) (wl 612 (lit c4))
  q406 : Ws → Eqn
  q406 c4 = eqn (CCZ023 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ []) (wp 498 c4)
  q407 : Ws → Eqn
  q407 c4 = eqn (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp 320 c4)
  q408 : Ws → Eqn
  q408 c4 = eqn (CCZ123 ∷ CS34 ∷ []) (CS34 ∷ CCZ123 ∷ []) (wl 492 (lit c4))
  q409 : Ws → Eqn
  q409 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q410 : Ws → Eqn
  q410 c4 = eqn (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ []) (wl 495 (lit c4))
  q411 : Ws → Eqn
  q411 c4 = eqn (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ []) (wl 490 (lit c4))
  q412 : Ws → Eqn
  q412 c4 = eqn (CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ []) (wl 613 (lit c4))
  q413 : Ws → Eqn
  q413 c4 = eqn (CX01 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX01 ∷ []) (wl 614 (lit c4))
  q414 : Ws → Eqn
  q414 c4 = eqn (CCZ034 ∷ []) (CX01 ∷ CCZ034 ∷ CX01 ∷ []) (wp 499 c4)

-- CXbc-box @0214203143: 17 steps
lem-CXbc-box-at0214203143 : Ws → ⟪ (CX01 ∷ Bx2-4013 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0214203143 c4 = derive (CX01 ∷ Bx2-4013 ∷ CX01 ∷ []) (Bx2-4013 ∷ CCZ034 ∷ [])
  (rw 1 (q403 c4) ∷
   rw 0 (q404 c4) ∷
   rw⁻ 1 (q405 c4) ∷
   rw 3 (q406 c4) ∷
   rw 2 (q404 c4) ∷
   rw 5 (q407 c4) ∷
   rw⁻ 9 (q408 c4) ∷
   rw 8 (q409 c4) ∷
   rw⁻ 7 (q410 c4) ∷
   rw 6 (q409 c4) ∷
   rw⁻ 5 (q411 c4) ∷
   rw⁻ 6 (q407 c4) ∷
   rw 4 (q412 c4) ∷
   rw⁻ 3 (q405 c4) ∷
   rw 4 (q413 c4) ∷
   rw⁻ 0 (q403 c4) ∷
   rw⁻ 1 (q414 c4) ∷ []) Eq.refl

private
  q415 : Ws → Eqn
  q415 c4 = eqn (CX10 ∷ Toff204 ∷ []) (Toff204 ∷ CX10 ∷ Toff214 ∷ []) (wp 500 c4)
  q416 : Ws → Eqn
  q416 c4 = eqn (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ123 ∷ []) (wl 615 (lit c4))
  q417 : Ws → Eqn
  q417 c4 = eqn (CCZ123 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ []) (wl 616 (lit c4))
  q418 : Ws → Eqn
  q418 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl 617 (lit c4))
  q419 : Ws → Eqn
  q419 c4 = eqn (CS34 ∷ Toff204 ∷ []) (Toff204 ∷ CS34 ∷ []) (wp 501 c4)
  q420 : Ws → Eqn
  q420 c4 = eqn (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ []) (wp 502 c4)
  q421 : Ws → Eqn
  q421 c4 = eqn (CS13⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4))
  q422 : Ws → Eqn
  q422 c4 = eqn (CS13 ∷ Toff204 ∷ []) (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4))
  q423 : Ws → Eqn
  q423 c4 = eqn (Toff204 ∷ Toff214 ∷ []) (Toff214 ∷ Toff204 ∷ []) (wp 503 c4)
  q424 : Ws → Eqn
  q424 c4 = eqn (CX10 ∷ Toff214 ∷ Toff214 ∷ []) (CX10 ∷ []) (wp 504 c4)
  q425 : Ws → Eqn
  q425 c4 = eqn (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ []) (wl 618 (lit c4))
  q426 : Ws → Eqn
  q426 c4 = eqn (CCZ134 ∷ []) (CX10 ∷ CCZ134 ∷ CX10 ∷ []) (wp 505 c4)

-- CXcb-box @0214203143: 18 steps
lem-CXcb-box-at0214203143 : Ws → ⟪ (CX10 ∷ Bx2-4013 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at0214203143 c4 = derive (CX10 ∷ Bx2-4013 ∷ CX10 ∷ []) (Bx2-4013 ∷ CCZ134 ∷ [])
  (rw 1 (q403 c4) ∷
   rw 0 (q415 c4) ∷
   rw⁻ 2 (q416 c4) ∷
   rw⁻ 1 (q417 c4) ∷
   rw 4 (q418 c4) ∷
   rw 8 (q419 c4) ∷
   rw 7 (q420 c4) ∷
   rw 6 (q421 c4) ∷
   rw 5 (q420 c4) ∷
   rw 4 (q422 c4) ∷
   rw⁻ 5 (q418 c4) ∷
   rw⁻ 3 (q423 c4) ∷
   rw 2 (q415 c4) ∷
   rw 3 (q424 c4) ∷
   rw⁻ 4 (q425 c4) ∷
   rw⁻ 3 (q417 c4) ∷
   rw⁻ 0 (q403 c4) ∷
   rw⁻ 1 (q426 c4) ∷ []) Eq.refl

private
  q427 : Ws → Eqn
  q427 c4 = eqn (Bx2-4103 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4)
  q428 : Ws → Eqn
  q428 c4 = eqn (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4)
  q429 : Ws → Eqn
  q429 c4 = eqn (CCZ023 ∷ CZ03 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ023 ∷ []) (wl 626 (lit c4))
  q430 : Ws → Eqn
  q430 c4 = eqn (CCZ023 ∷ CZ03 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff203 ∷ []) (wl 627 (lit c4))
  q431 : Ws → Eqn
  q431 c4 = eqn (CZ03 ∷ Toff214 ∷ []) (Toff214 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF214 (lit c4))
  q432 : Ws → Eqn
  q432 c4 = eqn (CCZ023 ∷ []) (CZ03 ∷ CCZ023 ∷ CZ03 ∷ []) (wl 628 (lit c4))

-- P-box @0214213043: 8 steps
lem-P-box-at0214213043 : Ws → ⟪ (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-P-box-at0214213043 c4 = derive (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) (Bx2-4103 ∷ [])
  (rw 1 (q427 c4) ∷
   rw⁻ 0 (q428 c4) ∷
   rw⁻ 1 (q429 c4) ∷
   rw⁻ 3 (q428 c4) ∷
   rw⁻ 4 (q430 c4) ∷
   rw 2 (q431 c4) ∷
   rw⁻ 3 (q432 c4) ∷
   rw⁻ 0 (q427 c4) ∷ []) Eq.refl
