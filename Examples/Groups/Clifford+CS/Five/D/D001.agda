{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D001 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0034 ; wl0037 ; wl0038 ; wl0044 ; wl0047 ; wl0070 ; wl0078 ; wl0084 ; wl0097 ; wl0099 ; wl0100 ; wl0101 ; wl0102 ; wl0103 ; wl0110 ; wl0111 ; wl0113 ; wl0116 ; wl0130 ; wl0143 ; wl0154 ; wl0158 ; wl0167 ; wl0168 ; wl0169 ; wl0170 ; wl0171 ; wl0172 ; wl0173 ; wl0174 ; wl0175 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0180 ; wl0181 ; wl0182 ; wl0183 ; wl0184 ; wl0185 ; wl0186 ; wl0187 ; wl0188 ; wl0189 ; wl0190 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0198 ; wl0199 ; wl0200 ; wl0201 ; wl0202 ; wl0203 ; wl0204 ; wl0205 ; wl0206 ; wl0207 ; wl0208 ; wl0209 ; wl0210 ; wl0211 ; wl0212 ; wl0213 ; wl0214 ; wl0215 ; wl0216 ; wl0217 ; wl0218 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0223 ; wl0224 ; wl0225 ; wl0226 ; wl0227 ; wl0228 ; wl0229 ; wl0230 ; wl0231 ; wl0232 ; wl0233 ; wl0234 ; wl0235 ; wl0236 ; wl0237 ; wl0238 ; wl0239 ; wl0240 ; wl0241 ; wl0242 ; wl0243 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0251 ; wp0001 ; wp0002 ; wp0003 ; wp0004 ; wp0005 ; wp0006 ; wp0007 ; wp0008 ; wp0009 ; wp0010 ; wp0011 ; wp0012 ; wp0013 ; wp0014 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0019 ; wp0020 ; wp0021 ; wp0022 ; wp0023 ; wp0024 ; wp0025 ; wp0026 ; wp0027 ; wp0028 ; wp0029 ; wp0030 ; wp0031 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0039 ; wp0040 ; wp0041 ; wp0042 ; wp0043 ; wp0044 ; wp0045 ; wp0046 ; wp0047 ; wp0048 ; wp0049 ; wp0050 ; wp0051 ; wp0052 ; wp0053 ; wp0054 ; wp0055 ; wp0056 ; wp0057 ; wp0058 ; wp0059)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CCZ034-CS12 ; lem-comm-CS12-CCZ034 ; lem-comm-CZ12-CCZ034 ; lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF203 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-BOX⟨1·034⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF301 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS03-TOFF214 ; lem-comm-CX12-CCZ034 ; lem-comm-TOFF214-CSd03 ; lem-comm-TOFF314-CS02 ; lem-comm-TOFF314-CSd02 ; lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-BOX⟨0·3124⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨1·4023⟩ ; lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF304 ; lem-nat-1-BOX⟨0·1243⟩ ; lem-nat-1-BOX⟨2·4013⟩ ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204 ; lem-nat-2-BOX⟨0·2143⟩ ; lem-nat-2-BOX⟨3·4012⟩ ; lem-nat-3-BOX⟨0·3142⟩ ; lem-nat-3-BOX⟨0·4123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-0-BOX⟨0·4132⟩ ; lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-0-BOX⟨3·4021⟩ ; lem-nat-0-BOX⟨3·4120⟩ ; lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·4023⟩ ; lem-nat-1-BOX⟨1·4032⟩ ; lem-nat-1-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨3·4021⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·2314⟩ ; lem-nat-2-BOX⟨2·4013⟩ ; lem-nat-2-BOX⟨2·4031⟩ ; lem-nat-2-TOFF104 ; lem-nat-3-BOX⟨0·3124⟩ ; lem-nat-3-BOX⟨0·3214⟩ ; lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨0·4213⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-BOX⟨2·4103⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·4203⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0143⟩ ; lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·4103⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-2-CCZ014 ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-BOX⟨2·0314⟩ ; lem-nat-3-BOX⟨2·0413⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-1-CZ01 ; lem-nat-1-CZ02)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) (wp0001 c4)

-- beta-form: 9 steps
lem-beta-form : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form c4 = derive (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q1 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q1 c4) ∷ []) Eq.refl

private
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0002 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ012 ∷ CS04 ∷ []) (CS04 ∷ CCZ012 ∷ []) (wp0003 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ012 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ012 ∷ []) (wp0004 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) (wl0167 (lit c4))

-- CCZ012-CCZ034: 7 steps
lem-CCZ012-CCZ034 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CCZ012-CCZ034 c4 = derive (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  (rw 1 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 0 (q2 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ []) (lem-CCZ012-CCZ034 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12 ∷ []) (c₃ (CS ↑) (CS • CS • CS))

-- P12-P34: 4 steps
lem-P12-P34 : Ws → ⟪ (CS12 ∷ CCZ012 ∷ CCZ034 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-P12-P34 c4 = derive (CS12 ∷ CCZ012 ∷ CCZ034 ∷ CS34⁻ ∷ []) (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ [])
  (rw 1 (q7 c4) ∷
   rw 0 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 1 (q10 c4) ∷ []) Eq.refl

private
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx0-1234 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ012 ∷ Toff012 ∷ CZ12 ∷ Z0 ∷ []) (Z0 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0168 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ034 ∷ Z0 ∷ []) (Z0 ∷ CCZ034 ∷ []) (wp0005 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Toff012 ∷ CCZ012 ∷ CZ12 ∷ Z0 ∷ []) (Z0 ∷ Toff012 ∷ CCZ012 ∷ []) (wl0169 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ034 ∷ []) (Z0 ∷ CCZ034 ∷ Z0 ∷ []) (wp0006 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CZ12 ∷ Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (Toff012 ∷ CCZ012 ∷ []) (wl0170 (lit c4))

-- Z0-beta: 8 steps
lem-Z0-beta : Ws → ⟪ (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-Z0-beta c4 = derive (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) (Bx0-1234 ∷ [])
  (rw 1 (q11 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw 3 (q17 c4) ∷
   rw⁻ 0 (q11 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (Z0 ∷ Bx0-1234 ∷ Z0 ∷ []) (Bx0-1234 ∷ []) (lem-Z0-beta c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Toff012 ∷ CCZ012 ∷ Z0 ∷ []) (Z0 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0171 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ012 ∷ Toff012 ∷ Z0 ∷ []) (Z0 ∷ Toff012 ∷ CCZ012 ∷ []) (wl0172 (lit c4))

-- beta-mirror: 6 steps
lem-beta-mirror : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-mirror c4 = derive (Bx0-1234 ∷ []) (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 1 (q11 c4) ∷
   rw⁻ 0 (q19 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 5 (q15 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = eqn (S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ []) [] (wl0173 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ CCZ012 ∷ Toff012 ∷ []) (wl0174 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ034 ∷ CS34⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ Toff034 ∷ CCZ034 ∷ []) (wp0007 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS12 ∷ CCZ012 ∷ CCZ034 ∷ CS34⁻ ∷ []) (CCZ034 ∷ CS34⁻ ∷ CS12 ∷ CCZ012 ∷ []) (lem-P12-P34 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (S0 ∷ K0 ∷ CCZ034 ∷ CS34⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ S0 ∷ K0 ∷ []) (wp0008 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ012 ∷ Toff012 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ []) (wl0175 (lit c4))

-- W-Q: 7 steps
lem-W-Q : Ws → ⟪ (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
lem-W-Q c4 = derive (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 0 (q25 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 4 (q21 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ012 ∷ Toff012 ∷ Toff012 ∷ CCZ012 ∷ []) [] (wl0176 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ012 ∷ Toff012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ []) (lem-W-Q c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) [] (wl0177 (lit c4))

-- V-Q: 3 steps
lem-V-Q : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-V-Q c4 = derive (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  (rw⁻ 4 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 0 (q29 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ034 ∷ []) (Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) (wp0009 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (lem-V-Q c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff034 ∷ CCZ034 ∷ Toff034 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ []) (wp0010 c4)

-- beta-T34: 4 steps
lem-beta-T34 : Ws → ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-beta-T34 c4 = derive (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  (rw 2 (q30 c4) ∷
   rw 7 (q30 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 5 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (K0 ∷ CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ K0 ∷ []) (wl0178 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) (wp0011 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ012 ∷ Toff012 ∷ K0 ∷ []) (K0 ∷ Toff012 ∷ CCZ012 ∷ []) (wl0179 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) (wp0012 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Z0 ∷ Z0 ∷ []) [] (wl0180 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff034 ∷ Z0 ∷ []) (Z0 ∷ Toff034 ∷ CZ34 ∷ []) (wp0013 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (Toff012 ∷ CZ34 ∷ []) (CZ34 ∷ Toff012 ∷ []) (c₃ (Toff) (CZ))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ012 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CZ))
  q41 : Ws → Eqn
  q41 c4 = eqn (CZ34 ∷ Toff034 ∷ CZ34 ∷ []) (Toff034 ∷ []) (wp0014 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ012 ∷ Toff012 ∷ Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-beta-T34 c4)

-- K0-beta: 16 steps
lem-K0-beta : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-K0-beta c4 = derive (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ [])
  (rw 1 (q11 c4) ∷
   rw 0 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 3 (q20 c4) ∷
   rw 2 (q38 c4) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw⁻ 5 (q40 c4) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 0 (q18 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (wl0181 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ []) (wl0182 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0183 (lit c4))

-- beta-T: 8 steps
lem-beta-T : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T c4 = derive (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  (rw 0 (q11 c4) ∷
   rw 4 (q7 c4) ∷
   rw 0 (q43 c4) ∷
   rw 2 (q16 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q44 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q45 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (CS12⁻ ∷ Toff012 ∷ S0 ∷ []) (S0 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0184 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ034 ∷ S0 ∷ []) (S0 ∷ CCZ034 ∷ []) (wp0015 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (S0 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CS12 ∷ S0 ∷ []) (wl0185 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ034 ∷ []) (S0 ∷ CCZ034 ∷ S0⁻ ∷ []) (wp0016 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (wl0186 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ034 ∷ CS12 ∷ []) (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS12⁻ ∷ CS12 ∷ []) [] (wl0187 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4)

-- S0-beta: 10 steps
lem-S0-beta : Ws → ⟪ (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-S0-beta c4 = derive (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) (Bx0-1234 ∷ [])
  (rw 1 (q11 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw⁻ 1 (q50 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (S0⁻ ∷ S0 ∷ []) [] (wl0188 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (S0 ∷ Bx0-1234 ∷ S0⁻ ∷ []) (Bx0-1234 ∷ []) (lem-S0-beta c4)

-- S0-beta-c: 2 steps
lem-S0-beta-c : Ws → ⟪ (S0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0 ∷ []) ⟫ʷ
lem-S0-beta-c c4 = derive (S0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0 ∷ [])
  (rw⁻ 2 (q54 c4) ∷
   rw 0 (q55 c4) ∷ []) Eq.refl

-- S0-beta-ci: 2 steps
lem-S0-beta-ci : Ws → ⟪ (S0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ
lem-S0-beta-ci c4 = derive (S0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0⁻ ∷ [])
  (rw⁻ 1 (q55 c4) ∷
   rw 0 (q54 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ []) (lem-K0-beta c4)

-- K0-pass: 1 steps
lem-K0-pass : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-K0-pass c4 = derive (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (K0⁻ ∷ K0 ∷ []) [] (wl0189 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (K0 ∷ Bx0-1234 ∷ K0⁻ ∷ []) (Bx0-1234 ∷ []) (lem-K0-pass c4)

-- K0-pass-c: 2 steps
lem-K0-pass-c : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-K0-pass-c c4 = derive (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  (rw⁻ 2 (q57 c4) ∷
   rw 0 (q58 c4) ∷ []) Eq.refl

-- K0-pass-ci: 2 steps
lem-K0-pass-ci : Ws → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-K0-pass-ci c4 = derive (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  (rw⁻ 1 (q58 c4) ∷
   rw 0 (q57 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (wl0190 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ012 ∷ Toff012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0191 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Toff012 ∷ CX34 ∷ []) (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁))
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ012 ∷ Toff012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ012 ∷ Toff012 ∷ []) (wp0017 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ012 ∷ Toff012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ Toff012 ∷ []) (wp0018 c4)

-- CCZ134-W: 9 steps
lem-CCZ134-W : Ws → ⟪ (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CCZ134-W c4 = derive (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ [])
  (rw 0 (q59 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw⁻ 2 (q59 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = eqn (CX10 ∷ CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CX10 ∷ []) (wl0192 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ034 ∷ CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ034 ∷ []) (wp0019 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ012 ∷ Toff012 ∷ CX10 ∷ []) (CX10 ∷ Toff012 ∷ CCZ012 ∷ []) (wl0193 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ034 ∷ CCZ134 ∷ []) (CX10 ∷ CCZ034 ∷ CX10 ∷ []) (wp0020 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ134 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ134 ∷ []) (lem-CCZ134-W c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ034 ∷ []) (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0021 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ012 ∷ CCZ034 ∷ CCZ012 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-mirror c4)

-- CX10-beta: 8 steps
lem-CX10-beta : Ws → ⟪ (CX10 ∷ Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-CX10-beta c4 = derive (CX10 ∷ Bx0-1234 ∷ CX10 ∷ []) (Bx0-1234 ∷ [])
  (rw 1 (q11 c4) ∷
   rw 0 (q64 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   rw 3 (q68 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   rw⁻ 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (CX10 ∷ CX10 ∷ []) [] (wl0194 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CX10 ∷ Bx0-1234 ∷ CX10 ∷ []) (Bx0-1234 ∷ []) (lem-CX10-beta c4)

-- CX10-beta-c: 2 steps
lem-CX10-beta-c : Ws → ⟪ (CX10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX10 ∷ []) ⟫ʷ
lem-CX10-beta-c c4 = derive (CX10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX10 ∷ [])
  (rw⁻ 2 (q71 c4) ∷
   rw 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (CS02 ∷ CCZ012 ∷ Toff012 ∷ []) (CS12⁻ ∷ Toff012 ∷ CS02 ∷ []) (wl0195 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp0022 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CS02 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CS12 ∷ CS02 ∷ []) (wl0196 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ034 ∷ []) (CS02 ∷ CCZ034 ∷ CS02⁻ ∷ []) (wp0023 c4)

-- CS20-beta: 10 steps
lem-CS20-beta : Ws → ⟪ (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-CS20-beta c4 = derive (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) (Bx0-1234 ∷ [])
  (rw 1 (q11 c4) ∷
   rw 0 (q73 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 5 (q76 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw⁻ 1 (q50 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wl0197 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS02 ∷ Bx0-1234 ∷ CS02⁻ ∷ []) (Bx0-1234 ∷ []) (lem-CS20-beta c4)

-- CS20-beta-c: 2 steps
lem-CS20-beta-c : Ws → ⟪ (CS02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02 ∷ []) ⟫ʷ
lem-CS20-beta-c c4 = derive (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ [])
  (rw⁻ 2 (q77 c4) ∷
   rw 0 (q78 c4) ∷ []) Eq.refl

-- CS20-beta-ci: 2 steps
lem-CS20-beta-ci : Ws → ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci c4 = derive (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ [])
  (rw⁻ 1 (q78 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (S0 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ K0⁻ ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) (wl0198 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (S0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0⁻ ∷ []) (lem-S0-beta-ci c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ []) (lem-K0-pass-ci c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CX10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CS02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ []) (lem-K0-pass-c c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (S0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ S0 ∷ []) (lem-S0-beta-c c4)

-- V-beta: 10 steps
lem-V-beta : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-V-beta c4 = derive (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q79 c4) ∷
   rw 7 (q80 c4) ∷
   rw 6 (q81 c4) ∷
   rw 5 (q82 c4) ∷
   rw 4 (q83 c4) ∷
   rw 3 (q82 c4) ∷
   rw 2 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 0 (q86 c4) ∷
   rw 1 (q79 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (Toff012 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ CCZ012 ∷ []) (lem-V-beta c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp0024 c4)

-- beta-inv: 7 steps
lem-beta-inv : Ws → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv c4 = derive (Bx0-1234 ∷ Bx0-1234 ∷ []) []
  (rw 1 (q70 c4) ∷
   rw⁻ 0 (q87 c4) ∷
   rw 2 (q11 c4) ∷
   rw 7 (q88 c4) ∷
   rw 0 (q29 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q88 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4))

-- beta-form @1221: 10 steps
lem-beta-form-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form-at1221 c4 = derive (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 1 (q11 c4) ∷
   rw⁻ 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw 5 (q93 c4) ∷
   rw 6 (q89 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ Toff012 ∷ []) (wl0199 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ []) (wl0200 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form-at1221 c4)

-- sym12: 4 steps
lem-sym12 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym12 c4 = derive (Bx0-1234 ∷ []) (Bx0-2134 ∷ [])
  (rw 0 (q11 c4) ∷
   rw 0 (q94 c4) ∷
   rw 3 (q95 c4) ∷
   rw⁻ 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw34 ∷ Bx0-1243 ∷ []) (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q100 : Ws → Eqn
  q100 c4 = eqn (Toff012 ∷ Sw34 ∷ []) (Sw34 ∷ Toff012 ∷ []) (c₃ (Toff) (Swap))
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 (lit c4))

-- beta-form @3443: 10 steps
lem-beta-form-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-form-at3443 c4 = derive (Bx0-1243 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 1 (q11 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw⁻ 1 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw⁻ 3 (q100 c4) ∷
   rw⁻ 4 (q99 c4) ∷
   rw 5 (q101 c4) ∷
   rw 6 (q97 c4) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ034 ∷ []) (CCZ034 ∷ []) (wp0025 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx0-1243 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form-at3443 c4)

-- sym34: 4 steps
lem-sym34 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym34 c4 = derive (Bx0-1234 ∷ []) (Bx0-1243 ∷ [])
  (rw 0 (q11 c4) ∷
   rw 2 (q102 c4) ∷
   rw 5 (q102 c4) ∷
   rw⁻ 0 (q103 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ012 ∷ Toff012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0201 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CS12 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ CS12 ∷ []) (wl0202 (lit c4))

-- CS12-beta: 6 steps
lem-CS12-beta : Ws → ⟪ (CS12 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS12 ∷ []) ⟫ʷ
lem-CS12-beta c4 = derive (CS12 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12 ∷ [])
  (rw 1 (q11 c4) ∷
   rw⁻ 0 (q104 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q105 c4) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 0 (q11 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ []) (CS12⁻ ∷ []) (wl0203 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CS12 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4)

-- CSd12-beta: 5 steps
lem-CSd12-beta : Ws → ⟪ (CS12⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSd12-beta c4 = derive (CS12⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12⁻ ∷ [])
  (rw⁻ 0 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   rw 1 (q107 c4) ∷
   rw 0 (q107 c4) ∷
   rw 1 (q106 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ012 ∷ []) (CX10 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ []) (wl0204 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (CS12⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4)

-- Cz-beta: 7 steps
lem-Cz-beta : Ws → ⟪ (CCZ012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Cz-beta c4 = derive (CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ [])
  (rw 0 (q108 c4) ∷
   rw 4 (q109 c4) ∷
   rw 3 (q83 c4) ∷
   rw 2 (q82 c4) ∷
   rw 1 (q84 c4) ∷
   rw 0 (q82 c4) ∷
   rw⁻ 1 (q108 c4) ∷ []) Eq.refl

-- W-beta: 3 steps
lem-W-beta : Ws → ⟪ (CCZ012 ∷ Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ []) ⟫ʷ
lem-W-beta c4 = derive (CCZ012 ∷ Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ [])
  (rw⁻ 3 (q29 c4) ∷
   rw⁻ 2 (q87 c4) ∷
   rw 0 (q27 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ012 ∷ CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ []) (wl0205 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ012 ∷ Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ Toff012 ∷ []) (lem-W-beta c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4)

-- T-beta: 4 steps
lem-T-beta : Ws → ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ
lem-T-beta c4 = derive (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q110 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4))

-- beta-T @2332: 8 steps
lem-beta-T-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at2332 c4 = derive (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 1 (q53 c4) ∷
   rw 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q113 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4))

-- beta-T @243243: 8 steps
lem-beta-T-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at243243 c4 = derive (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q120 c4) ∷
   rw 4 (q97 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Sw12 ∷ Bx0-2413 ∷ []) (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4))

-- beta-T @12243143: 8 steps
lem-beta-T-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at12243143 c4 = derive (Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q123 c4) ∷
   rw 3 (q124 c4) ∷
   rw 4 (q89 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (Sw23 ∷ Bx0-3412 ∷ []) (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4))

-- beta-T @13243142: 8 steps
lem-beta-T-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at13243142 c4 = derive (Bx0-3412 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw 0 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q127 c4) ∷
   rw 3 (q128 c4) ∷
   rw 4 (q113 c4) ∷ []) Eq.refl

private
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ012 ∷ Toff012 ∷ CX23 ∷ []) (CX23 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0206 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ034 ∷ CCZ024 ∷ CX23 ∷ []) (CX23 ∷ CCZ034 ∷ []) (wp0026 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CX23 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ CX23 ∷ []) (wl0207 (lit c4))
  q132 : Ws → Eqn
  q132 c4 = eqn (CCZ034 ∷ CCZ024 ∷ []) (CX23 ∷ CCZ034 ∷ CX23 ∷ []) (wp0027 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ024 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0028 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0208 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) (wp0029 c4)
  q136 : Ws → Eqn
  q136 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) (wp0030 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp0031 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) (wp0032 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) (wp0033 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)

-- CX23-beta: 17 steps
lem-CX23-beta : Ws → ⟪ (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CX23-beta c4 = derive (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  (rw 1 (q11 c4) ∷
   rw⁻ 0 (q129 c4) ∷
   rw⁻ 2 (q130 c4) ∷
   rw 4 (q131 c4) ∷
   rw⁻ 6 (q132 c4) ∷
   rw 3 (q133 c4) ∷
   rw 6 (q134 c4) ∷
   rw⁻ 10 (q135 c4) ∷
   rw 9 (q136 c4) ∷
   rw⁻ 8 (q137 c4) ∷
   rw 7 (q136 c4) ∷
   rw⁻ 6 (q138 c4) ∷
   rw⁻ 7 (q134 c4) ∷
   rw 5 (q139 c4) ∷
   rw⁻ 7 (q140 c4) ∷
   rw 6 (q141 c4) ∷
   rw⁻ 0 (q11 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff013 ∷ CCZ123 ∷ CX32 ∷ []) (CX32 ∷ CCZ012 ∷ Toff012 ∷ []) (wl0209 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (CCZ034 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ []) (wp0035 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ123 ∷ Toff013 ∷ CCZ013 ∷ Toff012 ∷ CCZ012 ∷ CX32 ∷ []) (CX32 ∷ Toff012 ∷ CCZ012 ∷ []) (wl0210 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ034 ∷ []) (CX32 ∷ CCZ034 ∷ CX32 ∷ []) (wp0036 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0211 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) (wp0037 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ034 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ034 ∷ []) (wp0038 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp0039 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0212 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff013 ∷ CCZ013 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) (wp0040 c4)

-- CX32-beta: 16 steps
lem-CX32-beta : Ws → ⟪ (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-CX32-beta c4 = derive (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  (rw 1 (q11 c4) ∷
   rw⁻ 0 (q142 c4) ∷
   rw⁻ 5 (q143 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw⁻ 11 (q145 c4) ∷
   rw 4 (q146 c4) ∷
   rw⁻ 8 (q147 c4) ∷
   rw 7 (q136 c4) ∷
   rw⁻ 6 (q148 c4) ∷
   rw 5 (q136 c4) ∷
   rw⁻ 4 (q149 c4) ∷
   rw⁻ 5 (q146 c4) ∷
   rw 5 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw⁻ 0 (q68 c4) ∷
   rw⁻ 1 (q11 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ012 ∷ []) (wp0041 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (CCZ124 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ []) (wp0042 c4)

-- c124-beta: 20 steps
lem-c124-beta : Ws → ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-c124-beta c4 = derive (CCZ124 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  (rw 1 (q11 c4) ∷
   rw⁻ 0 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q134 c4) ∷
   rw⁻ 6 (q135 c4) ∷
   rw 5 (q136 c4) ∷
   rw⁻ 4 (q137 c4) ∷
   rw 3 (q136 c4) ∷
   rw⁻ 2 (q138 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw 3 (q153 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 5 (q134 c4) ∷
   rw⁻ 9 (q135 c4) ∷
   rw 8 (q136 c4) ∷
   rw⁻ 7 (q137 c4) ∷
   rw 6 (q136 c4) ∷
   rw⁻ 5 (q138 c4) ∷
   rw⁻ 6 (q134 c4) ∷
   rw⁻ 0 (q11 c4) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) (wl0213 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (CCZ012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ012 ∷ []) (wp0043 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ []) (wp0044 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) (wl0214 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (CS14⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS14⁻ ∷ []) (wp0045 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ []) (wp0046 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) (wp0047 c4)

-- c134-beta: 32 steps
lem-c134-beta : Ws → ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ
lem-c134-beta c4 = derive (CCZ134 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ [])
  (rw 1 (q11 c4) ∷
   rw 0 (q59 c4) ∷
   rw⁻ 4 (q154 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 2 (q155 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 0 (q156 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw 1 (q59 c4) ∷
   rw 5 (q157 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   rw 3 (q158 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 1 (q159 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 2 (q160 c4) ∷
   rw 3 (q59 c4) ∷
   rw 7 (q157 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 5 (q158 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   rw 3 (q159 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 8 (q154 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q155 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 4 (q156 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw⁻ 5 (q160 c4) ∷
   rw⁻ 0 (q11 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = eqn (CX23 ∷ CX32 ∷ CX23 ∷ []) (Sw23 ∷ []) (wl0215 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (CX23 ∷ Bx0-1234 ∷ CX23 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (CX32 ∷ CX32 ∷ []) [] (wl0216 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (CX32 ∷ Bx0-1234 ∷ CX32 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ []) (lem-CX32-beta c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ124 ∷ CCZ134 ∷ []) (CX32 ∷ CCZ124 ∷ CX32 ∷ []) (wl0217 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (CX23 ∷ CX23 ∷ []) [] (wl0218 (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (CCZ134 ∷ CCZ124 ∷ []) (CX23 ∷ CCZ134 ∷ CX23 ∷ []) (wl0219 (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (CX23 ∷ CCZ124 ∷ CCZ134 ∷ CX23 ∷ []) (wl0220 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (CCZ124 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (CCZ134 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ134 ∷ []) (lem-c134-beta c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) [] (wl0221 (lit c4))

-- SW23-beta: 14 steps
lem-SW23-beta : Ws → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-SW23-beta c4 = derive (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (Bx0-1234 ∷ [])
  (rw⁻ 0 (q161 c4) ∷
   rw⁻ 4 (q161 c4) ∷
   rw 2 (q162 c4) ∷
   rw⁻ 3 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw⁻ 3 (q165 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw⁻ 0 (q167 c4) ∷
   rw⁻ 4 (q166 c4) ∷
   rw 2 (q162 c4) ∷
   rw⁻ 4 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q171 c4) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (Bx0-1234 ∷ []) (lem-SW23-beta c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw23 ∷ Bx1-034 ∷ []) (Bx1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·034⟩ (lit c4))

-- sym23: 10 steps
lem-sym23 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym23 c4 = derive (Bx0-1234 ∷ []) (Bx0-1324 ∷ [])
  (rw⁻ 0 (q172 c4) ∷
   re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   rw 0 (q173 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q115 c4) ∷
   rw 4 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   re 0 6 (Bx0-1324 ∷ []) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = eqn (CS02 ∷ CS02 ∷ []) (CZ02 ∷ []) (wl0222 (lit c4))

-- CZ10-beta-c: 4 steps
lem-CZ10-beta-c : Ws → ⟪ (CZ02 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ []) ⟫ʷ
lem-CZ10-beta-c c4 = derive (CZ02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ [])
  (rw⁻ 0 (q175 c4) ∷
   rw 1 (q84 c4) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q175 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn [] [] (wl0223 (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (Bx0-1234 ∷ Bx0-1234 ∷ []) [] (lem-beta-inv c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wl0224 (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (CZ14 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) [] (wp0048 c4)

-- BOXd-BOX: 22 steps
lem-BOXd-BOX : Ws → ⟪ (Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-BOXd-BOX c4 = derive (Bx⁻0-1234 ∷ []) (Bx0-1234 ∷ [])
  (rw 1 (q176 c4) ∷
   rw⁻ 1 (q177 c4) ∷
   re 0 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 6 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   rw 5 (q45 c4) ∷
   rw 4 (q178 c4) ∷
   re 3 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) ∷
   re 3 1 (CZ14 ∷ []) ∷
   re 6 1 (CZ14 ∷ []) ∷
   re 9 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 11 1 (CZ14 ∷ []) ∷
   re 14 1 (CZ14 ∷ []) ∷
   rw 3 (q179 c4) ∷
   rw 2 (q178 c4) ∷
   rw 1 (q45 c4) ∷
   re 0 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) ∷
   re 0 1 (CZ14 ∷ []) ∷
   re 3 1 (CZ14 ∷ []) ∷
   re 6 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 8 1 (CZ14 ∷ []) ∷
   re 11 1 (CZ14 ∷ []) ∷
   rw 0 (q179 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0225 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))
  q182 : Ws → Eqn
  q182 c4 = eqn (CX24 ∷ Toff012 ∷ []) (Toff012 ∷ CX24 ∷ []) (wp0049 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))
  q184 : Ws → Eqn
  q184 c4 = eqn (CS23 ∷ Toff012 ∷ []) (Toff012 ∷ CS23 ∷ []) (wl0226 (lit c4))

-- auto TOFF012 | CCZ324: 7 steps
lem-auto-TOFF012-∣-CCZ324 : Ws → ⟪ (Toff012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324 c4 = derive (Toff012 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff012 ∷ [])
  (rw 1 (q180 c4) ∷
   rw 0 (q181 c4) ∷
   rw⁻ 1 (q182 c4) ∷
   rw 2 (q183 c4) ∷
   rw⁻ 3 (q182 c4) ∷
   rw⁻ 4 (q184 c4) ∷
   rw⁻ 0 (q180 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0227 (lit c4))
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q187 : Ws → Eqn
  q187 c4 = eqn (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) (wp0050 c4)

-- auto CCZ012 | CCZ314: 7 steps
lem-auto-CCZ012-∣-CCZ314 : Ws → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314 c4 = derive (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  (rw 1 (q185 c4) ∷
   rw 0 (q186 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q187 c4) ∷
   rw 4 (q154 c4) ∷
   rw⁻ 0 (q185 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = eqn (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0051 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (CCZ012 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ []) (wp0052 c4)

-- auto CCZ012 | CCZ304: 7 steps
lem-auto-CCZ012-∣-CCZ304 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304 c4 = derive (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  (rw 1 (q188 c4) ∷
   rw 0 (q186 c4) ∷
   rw 1 (q189 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q189 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 0 (q188 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = eqn (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ []) (wp0053 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (CCZ012 ∷ K3 ∷ []) (K3 ∷ CCZ012 ∷ []) (wl0228 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ304 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CCZ012 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ012 ∷ []) (wl0229 (lit c4))

-- auto CCZ012 | TOFF304: 5 steps
lem-auto-CCZ012-∣-TOFF304 : Ws → ⟪ (CCZ012 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304 c4 = derive (CCZ012 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ012 ∷ [])
  (rw⁻ 1 (q190 c4) ∷
   rw 0 (q191 c4) ∷
   rw 1 (q192 c4) ∷
   rw 2 (q193 c4) ∷
   rw 0 (q190 c4) ∷ []) Eq.refl

-- beta-form @2332: 10 steps
lem-beta-form-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-form-at2332 c4 = derive (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 1 (q11 c4) ∷
   rw 0 (q173 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   rw 3 (q115 c4) ∷
   rw 4 (q173 c4) ∷
   rw 5 (q116 c4) ∷
   rw 6 (q113 c4) ∷ []) Eq.refl

private
  q194 : Ws → Eqn
  q194 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q195 : Ws → Eqn
  q195 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q197 : Ws → Eqn
  q197 c4 = eqn (Toff012 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ324 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4))

-- auto TOFF012 | CCZ324 @0110: 7 steps
lem-auto-TOFF012-∣-CCZ324-at0110 : Ws → ⟪ (Toff102 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at0110 c4 = derive (Toff102 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff102 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q195 c4) ∷
   rw 2 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw 0 (q196 c4) ∷
   rw 1 (q198 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 (lit c4))
  q201 : Ws → Eqn
  q201 c4 = eqn (Toff102 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at0110 c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 (lit c4))
  q203 : Ws → Eqn
  q203 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4))

-- auto TOFF012 | CCZ324 @021021: 7 steps
lem-auto-TOFF012-∣-CCZ324-at021021 : Ws → ⟪ (Toff201 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at021021 c4 = derive (Toff201 ∷ CCZ134 ∷ []) (CCZ134 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q199 c4) ∷
   rw⁻ 2 (q200 c4) ∷
   rw 1 (q201 c4) ∷
   rw⁻ 0 (q202 c4) ∷
   rw 1 (q203 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 (lit c4))
  q205 : Ws → Eqn
  q205 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (Toff201 ∷ CCZ134 ∷ []) (CCZ134 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at021021 c4)
  q207 : Ws → Eqn
  q207 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4))
  q208 : Ws → Eqn
  q208 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4))

-- auto TOFF012 | CCZ324 @03102132: 7 steps
lem-auto-TOFF012-∣-CCZ324-at03102132 : Ws → ⟪ (Toff301 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at03102132 c4 = derive (Toff301 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q204 c4) ∷
   rw 2 (q205 c4) ∷
   rw 1 (q206 c4) ∷
   rw 0 (q207 c4) ∷
   rw 1 (q208 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 (lit c4))
  q211 : Ws → Eqn
  q211 c4 = eqn (Toff301 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at03102132 c4)
  q212 : Ws → Eqn
  q212 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4))

-- auto TOFF012 | CCZ324 @031031: 7 steps
lem-auto-TOFF012-∣-CCZ324-at031031 : Ws → ⟪ (Toff302 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff302 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at031031 c4 = derive (Toff302 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q209 c4) ∷
   rw⁻ 2 (q210 c4) ∷
   rw 1 (q211 c4) ∷
   rw⁻ 0 (q210 c4) ∷
   rw 1 (q212 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0110 (lit c4))
  q214 : Ws → Eqn
  q214 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4))
  q215 : Ws → Eqn
  q215 c4 = eqn (Toff302 ∷ CCZ124 ∷ []) (CCZ124 ∷ Toff302 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at031031 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4))

-- auto TOFF012 | CCZ324 @0330: 7 steps
lem-auto-TOFF012-∣-CCZ324-at0330 : Ws → ⟪ (Toff312 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff312 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ324-at0330 c4 = derive (Toff312 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q214 c4) ∷
   rw 1 (q215 c4) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q217 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

private
  q218 : Ws → Eqn
  q218 c4 = eqn (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ314 c4)

-- auto CCZ012 | CCZ314 @2332: 7 steps
lem-auto-CCZ012-∣-CCZ314-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at2332 c4 = derive (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q205 c4) ∷
   rw 1 (q218 c4) ∷
   rw 0 (q207 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = eqn (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at2332 c4)
  q220 : Ws → Eqn
  q220 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4))

-- auto CCZ012 | CCZ314 @122331: 7 steps
lem-auto-CCZ012-∣-CCZ314-at122331 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at122331 c4 = derive (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q124 c4) ∷
   rw⁻ 2 (q210 c4) ∷
   rw 1 (q219 c4) ∷
   rw⁻ 0 (q210 c4) ∷
   rw 1 (q220 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q221 : Ws → Eqn
  q221 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 (lit c4))
  q222 : Ws → Eqn
  q222 c4 = eqn (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at122331 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 (lit c4))

-- auto CCZ012 | CCZ314 @01122330: 7 steps
lem-auto-CCZ012-∣-CCZ314-at01122330 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at01122330 c4 = derive (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 2 (q214 c4) ∷
   rw 1 (q222 c4) ∷
   rw 0 (q216 c4) ∷
   rw⁻ 1 (q223 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4))
  q225 : Ws → Eqn
  q225 c4 = eqn (CCZ012 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF304 c4)
  q226 : Ws → Eqn
  q226 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 (lit c4))

-- auto CCZ012 | TOFF304 @2332: 7 steps
lem-auto-CCZ012-∣-TOFF304-at2332 : Ws → ⟪ (CCZ013 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at2332 c4 = derive (CCZ013 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q224 c4) ∷
   rw 1 (q225 c4) ∷
   rw 0 (q226 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

private
  q227 : Ws → Eqn
  q227 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4))
  q228 : Ws → Eqn
  q228 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 (lit c4))
  q229 : Ws → Eqn
  q229 c4 = eqn (CCZ013 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at2332 c4)
  q230 : Ws → Eqn
  q230 c4 = eqn (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 (lit c4))
  q231 : Ws → Eqn
  q231 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4))

-- auto CCZ012 | TOFF304 @243243: 7 steps
lem-auto-CCZ012-∣-TOFF304-at243243 : Ws → ⟪ (CCZ014 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at243243 c4 = derive (CCZ014 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q228 c4) ∷
   rw 1 (q229 c4) ∷
   rw 0 (q230 c4) ∷
   rw 1 (q231 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q232 : Ws → Eqn
  q232 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 (lit c4))
  q234 : Ws → Eqn
  q234 c4 = eqn (CCZ014 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at243243 c4)
  q235 : Ws → Eqn
  q235 c4 = eqn (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 (lit c4))
  q236 : Ws → Eqn
  q236 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4))

-- auto CCZ012 | TOFF304 @12243143: 7 steps
lem-auto-CCZ012-∣-TOFF304-at12243143 : Ws → ⟪ (CCZ024 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at12243143 c4 = derive (CCZ024 ∷ Toff103 ∷ []) (Toff103 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q233 c4) ∷
   rw 1 (q234 c4) ∷
   rw 0 (q235 c4) ∷
   rw 1 (q236 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ024 ∷ Toff103 ∷ []) (Toff103 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at12243143 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) (wl0102 (lit c4))

-- auto CCZ012 | TOFF304 @0112243043: 7 steps
lem-auto-CCZ012-∣-TOFF304-at0112243043 : Ws → ⟪ (CCZ124 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at0112243043 c4 = derive (CCZ124 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q237 c4) ∷
   rw 1 (q238 c4) ∷
   rw 0 (q239 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4))

-- auto CCZ012 | CCZ304 @2332: 7 steps
lem-auto-CCZ012-∣-CCZ304-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at2332 c4 = derive (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q240 c4) ∷
   rw 1 (q192 c4) ∷
   rw 0 (q116 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4))
  q242 : Ws → Eqn
  q242 c4 = eqn (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at2332 c4)

-- auto CCZ012 | CCZ304 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ304-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at243243 c4 = derive (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q241 c4) ∷
   rw 1 (q242 c4) ∷
   rw 0 (q120 c4) ∷
   rw 1 (q231 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at243243 c4)

-- auto CCZ012 | CCZ304 @12243143: 7 steps
lem-auto-CCZ012-∣-CCZ304-at12243143 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at12243143 c4 = derive (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q220 c4) ∷
   rw 1 (q243 c4) ∷
   rw 0 (q124 c4) ∷
   rw 1 (q236 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q244 : Ws → Eqn
  q244 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 (lit c4))
  q245 : Ws → Eqn
  q245 c4 = eqn (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at12243143 c4)

-- auto CCZ012 | CCZ304 @0112243043: 7 steps
lem-auto-CCZ012-∣-CCZ304-at0112243043 : Ws → ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at0112243043 c4 = derive (CCZ124 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q216 c4) ∷
   rw⁻ 2 (q244 c4) ∷
   rw 1 (q245 c4) ∷
   rw⁻ 0 (q244 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1324 ∷ []) (lem-sym23 c4)
  q247 : Ws → Eqn
  q247 c4 = eqn (Bx0-1324 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (lem-beta-form-at2332 c4)
  q248 : Ws → Eqn
  q248 c4 = eqn (Toff312 ∷ Toff312 ∷ []) [] (wl0230 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff012 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ013 ∷ Toff013 ∷ Toff312 ∷ []) (wl0231 (lit c4))
  q250 : Ws → Eqn
  q250 c4 = eqn (Toff312 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff312 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at0330 c4)
  q251 : Ws → Eqn
  q251 c4 = eqn (CCZ123 ∷ Toff012 ∷ CCZ012 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff312 ∷ Toff013 ∷ CCZ013 ∷ Toff312 ∷ []) (wl0232 (lit c4))
  q252 : Ws → Eqn
  q252 c4 = eqn (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at01122330 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff012 ∷ CCZ012 ∷ []) (CCZ024 ∷ CCZ124 ∷ []) (wp0054 c4)
  q254 : Ws → Eqn
  q254 c4 = eqn (CCZ124 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at0112243043 c4)
  q255 : Ws → Eqn
  q255 c4 = eqn (CCZ124 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at0112243043 c4)

-- T312-beta: 17 steps
lem-T312-beta : Ws → ⟪ (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta c4 = derive (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  (rw 1 (q246 c4) ∷
   rw 1 (q247 c4) ∷
   rw⁻ 3 (q248 c4) ∷
   rw⁻ 0 (q249 c4) ∷
   rw 5 (q250 c4) ∷
   rw⁻ 9 (q248 c4) ∷
   rw⁻ 6 (q251 c4) ∷
   rw 11 (q250 c4) ∷
   rw 12 (q248 c4) ∷
   rw 4 (q252 c4) ∷
   rw 5 (q150 c4) ∷
   rw 2 (q253 c4) ∷
   rw 3 (q254 c4) ∷
   rw 4 (q255 c4) ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 0 (q247 c4) ∷
   rw⁻ 0 (q246 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = eqn (CX23 ∷ Toff214 ∷ Toff314 ∷ CX23 ∷ []) (Toff214 ∷ []) (wl0233 (lit c4))
  q257 : Ws → Eqn
  q257 c4 = eqn (CS03⁻ ∷ []) (CX23 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) (wl0234 (lit c4))
  q258 : Ws → Eqn
  q258 c4 = eqn (Toff214 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4))
  q259 : Ws → Eqn
  q259 c4 = eqn (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ []) (wl0235 (lit c4))
  q260 : Ws → Eqn
  q260 c4 = eqn (CX23 ∷ Toff214 ∷ Toff314 ∷ []) (Toff214 ∷ CX23 ∷ []) (wl0236 (lit c4))

-- F0-A: 9 steps
lem-F0-A : Ws → ⟪ (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ []) ⟫ʷ
lem-F0-A c4 = derive (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q166 c4) ∷
   rw⁻ 4 (q166 c4) ∷
   rw⁻ 9 (q166 c4) ∷
   rw 1 (q256 c4) ∷
   rw⁻ 2 (q257 c4) ∷
   rw 1 (q258 c4) ∷
   rw⁻ 0 (q259 c4) ∷
   rw⁻ 4 (q260 c4) ∷
   rw 3 (q166 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = eqn (CCZ023 ∷ []) (CS02 ∷ CS03 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (wl0237 (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff214 ∷ []) (wl0238 (lit c4))
  q263 : Ws → Eqn
  q263 c4 = eqn (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ []) (lem-F0-A c4)
  q264 : Ws → Eqn
  q264 c4 = eqn (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS02⁻ ∷ []) (wl0239 (lit c4))

-- F0-B: 6 steps
lem-F0-B : Ws → ⟪ (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-F0-B c4 = derive (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ [])
  (rw 2 (q261 c4) ∷
   rw⁻ 7 (q262 c4) ∷
   rw⁻ 4 (q263 c4) ∷
   rw 4 (q176 c4) ∷
   rw 6 (q264 c4) ∷
   rw 4 (q262 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = eqn (Toff314 ∷ CS02 ∷ []) (CS02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CS02 (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (CS03 ∷ Toff214 ∷ []) (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 (lit c4))
  q267 : Ws → Eqn
  q267 c4 = eqn (CS02⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS02⁻ ∷ []) (wl0240 (lit c4))
  q268 : Ws → Eqn
  q268 c4 = eqn (Toff314 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4))
  q269 : Ws → Eqn
  q269 c4 = eqn (CS02⁻ ∷ CS03 ∷ []) (CS03 ∷ CS02⁻ ∷ []) (wl0241 (lit c4))

-- F0-C: 8 steps
lem-F0-C : Ws → ⟪ (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-F0-C c4 = derive (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  (rw 1 (q265 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 3 (q266 c4) ∷
   rw⁻ 2 (q262 c4) ∷
   rw⁻ 6 (q267 c4) ∷
   rw 5 (q268 c4) ∷
   rw⁻ 4 (q269 c4) ∷
   rw 3 (q268 c4) ∷ []) Eq.refl

-- beta-T @1221: 8 steps
lem-beta-T-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at1221 c4 = derive (Bx0-2134 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 1 (q53 c4) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q92 c4) ∷
   rw 3 (q93 c4) ∷
   rw 4 (q89 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = eqn (Sw23 ∷ Bx0-3124 ∷ []) (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4))
  q271 : Ws → Eqn
  q271 c4 = eqn (Bx0-2134 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at1221 c4)

-- beta-T @132132: 8 steps
lem-beta-T-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at132132 c4 = derive (Bx0-3124 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q270 c4) ∷
   rw 1 (q271 c4) ∷
   rw 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q113 c4) ∷ []) Eq.refl

private
  q272 : Ws → Eqn
  q272 c4 = eqn (Sw34 ∷ Bx0-4123 ∷ []) (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4))
  q273 : Ws → Eqn
  q273 c4 = eqn (Bx0-3124 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at132132 c4)

-- beta-T @14213243: 8 steps
lem-beta-T-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at14213243 c4 = derive (Bx0-4123 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q272 c4) ∷
   rw 1 (q273 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q120 c4) ∷
   rw 4 (q97 c4) ∷ []) Eq.refl

private
  q274 : Ws → Eqn
  q274 c4 = eqn (Sw01 ∷ Bx1-4023 ∷ []) (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (Bx0-4123 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at14213243 c4)
  q276 : Ws → Eqn
  q276 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4))

-- beta-T @0114203243: 8 steps
lem-beta-T-at0114203243 : Ws → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0114203243 c4 = derive (Bx1-4023 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q274 c4) ∷
   rw 1 (q275 c4) ∷
   rw 0 (q276 c4) ∷
   rw⁻ 1 (q223 c4) ∷
   rw 2 (q276 c4) ∷
   rw⁻ 3 (q223 c4) ∷
   rw 4 (q194 c4) ∷ []) Eq.refl

private
  q277 : Ws → Eqn
  q277 c4 = eqn (Sw12 ∷ Bx2-4013 ∷ []) (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ (lit c4))
  q278 : Ws → Eqn
  q278 c4 = eqn (Bx1-4023 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at0114203243 c4)
  q279 : Ws → Eqn
  q279 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4))
  q280 : Ws → Eqn
  q280 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 (lit c4))

-- beta-T @0214203143: 8 steps
lem-beta-T-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q277 c4) ∷
   rw 1 (q278 c4) ∷
   rw 0 (q279 c4) ∷
   rw⁻ 1 (q280 c4) ∷
   rw 2 (q279 c4) ∷
   rw⁻ 3 (q280 c4) ∷
   rw 4 (q89 c4) ∷ []) Eq.refl

private
  q281 : Ws → Eqn
  q281 c4 = eqn (Sw23 ∷ Bx3-4012 ∷ []) (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ (lit c4))
  q282 : Ws → Eqn
  q282 c4 = eqn (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0214203143 c4)
  q283 : Ws → Eqn
  q283 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 (lit c4))

-- beta-T @0314203142: 8 steps
lem-beta-T-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q281 c4) ∷
   rw 1 (q282 c4) ∷
   rw 0 (q224 c4) ∷
   rw⁻ 1 (q283 c4) ∷
   rw 2 (q224 c4) ∷
   rw⁻ 3 (q283 c4) ∷
   rw 4 (q113 c4) ∷ []) Eq.refl

private
  q284 : Ws → Eqn
  q284 c4 = eqn (Sw01 ∷ Bx3-4102 ∷ []) (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ (lit c4))
  q285 : Ws → Eqn
  q285 c4 = eqn (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0314203142 c4)
  q286 : Ws → Eqn
  q286 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 (lit c4))

-- beta-T @0314213042: 8 steps
lem-beta-T-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q284 c4) ∷
   rw 1 (q285 c4) ∷
   rw 0 (q286 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 2 (q286 c4) ∷
   rw⁻ 3 (q221 c4) ∷
   rw 4 (q194 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = eqn (Bx0-1234 ∷ []) (Bx0-1243 ∷ []) (lem-sym34 c4)
  q288 : Ws → Eqn
  q288 c4 = eqn (Sw12 ∷ Bx0-1243 ∷ []) (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ (lit c4))

-- sym34 @1221: 5 steps
lem-sym34-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym34-at1221 c4 = derive (Bx0-2134 ∷ []) (Bx0-2143 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 1 (q287 c4) ∷
   rw 0 (q288 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q289 : Ws → Eqn
  q289 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2143 ∷ []) (lem-sym34-at1221 c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (Sw23 ∷ Bx0-2143 ∷ []) (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ (lit c4))

-- sym34 @132132: 5 steps
lem-sym34-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym34-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-3142 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q270 c4) ∷
   rw 1 (q289 c4) ∷
   rw 0 (q290 c4) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

private
  q291 : Ws → Eqn
  q291 c4 = eqn (Bx0-3124 ∷ []) (Bx0-3142 ∷ []) (lem-sym34-at132132 c4)
  q292 : Ws → Eqn
  q292 c4 = eqn (Sw34 ∷ Bx0-3142 ∷ []) (Bx0-4132 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3142⟩ (lit c4))

-- sym34 @14213243: 5 steps
lem-sym34-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym34-at14213243 c4 = derive (Bx0-4123 ∷ []) (Bx0-4132 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q272 c4) ∷
   rw 1 (q291 c4) ∷
   rw 0 (q292 c4) ∷
   rw 1 (q97 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = eqn (Bx0-4123 ∷ []) (Bx0-4132 ∷ []) (lem-sym34-at14213243 c4)
  q294 : Ws → Eqn
  q294 c4 = eqn (Sw01 ∷ Bx0-4132 ∷ []) (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ (lit c4))

-- sym34 @0114203243: 5 steps
lem-sym34-at0114203243 : Ws → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ []) ⟫ʷ
lem-sym34-at0114203243 c4 = derive (Bx1-4023 ∷ []) (Bx1-4032 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q274 c4) ∷
   rw 1 (q293 c4) ∷
   rw 0 (q294 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q295 : Ws → Eqn
  q295 c4 = eqn (Bx1-4023 ∷ []) (Bx1-4032 ∷ []) (lem-sym34-at0114203243 c4)
  q296 : Ws → Eqn
  q296 c4 = eqn (Sw12 ∷ Bx1-4032 ∷ []) (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ (lit c4))

-- sym34 @0214203143: 5 steps
lem-sym34-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym34-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-4031 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q277 c4) ∷
   rw 1 (q295 c4) ∷
   rw 0 (q296 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q297 : Ws → Eqn
  q297 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4)
  q298 : Ws → Eqn
  q298 c4 = eqn (Sw23 ∷ Bx2-4031 ∷ []) (Bx3-4021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4031⟩ (lit c4))

-- sym34 @0314203142: 5 steps
lem-sym34-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym34-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-4021 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q281 c4) ∷
   rw 1 (q297 c4) ∷
   rw 0 (q298 c4) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

private
  q299 : Ws → Eqn
  q299 c4 = eqn (Bx3-4012 ∷ []) (Bx3-4021 ∷ []) (lem-sym34-at0314203142 c4)
  q300 : Ws → Eqn
  q300 c4 = eqn (Sw01 ∷ Bx3-4021 ∷ []) (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ (lit c4))

-- sym34 @0314213042: 5 steps
lem-sym34-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym34-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-4120 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q284 c4) ∷
   rw 1 (q299 c4) ∷
   rw 0 (q300 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q301 : Ws → Eqn
  q301 c4 = eqn (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) (wl0143 (lit c4))
  q302 : Ws → Eqn
  q302 c4 = eqn (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4)
  q303 : Ws → Eqn
  q303 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4))

-- T312-beta @1221: 8 steps
lem-T312-beta-at1221 : Ws → ⟪ (Toff312 ∷ Bx0-2134 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at1221 c4 = derive (Toff312 ∷ Bx0-2134 ∷ Toff312 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q301 c4) ∷
   rw 2 (q90 c4) ∷
   rw 3 (q301 c4) ∷
   rw 1 (q302 c4) ∷
   rw 0 (q303 c4) ∷
   rw⁻ 1 (q210 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q304 : Ws → Eqn
  q304 c4 = eqn (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) (wl0158 (lit c4))
  q305 : Ws → Eqn
  q305 c4 = eqn (Toff312 ∷ Bx0-2134 ∷ Toff312 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ []) (lem-T312-beta-at1221 c4)
  q306 : Ws → Eqn
  q306 c4 = eqn (Sw23 ∷ Bx0-2134 ∷ []) (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4))

-- T312-beta @132132: 8 steps
lem-T312-beta-at132132 : Ws → ⟪ (Toff213 ∷ Bx0-3124 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at132132 c4 = derive (Toff213 ∷ Bx0-3124 ∷ Toff213 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q304 c4) ∷
   rw 2 (q270 c4) ∷
   rw 3 (q304 c4) ∷
   rw 1 (q305 c4) ∷
   rw 0 (q306 c4) ∷
   rw 1 (q205 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

private
  q307 : Ws → Eqn
  q307 c4 = eqn (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 (lit c4))
  q308 : Ws → Eqn
  q308 c4 = eqn (Toff213 ∷ Bx0-3124 ∷ Toff213 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ []) (lem-T312-beta-at132132 c4)
  q309 : Ws → Eqn
  q309 c4 = eqn (Sw34 ∷ Bx0-3124 ∷ []) (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ (lit c4))
  q310 : Ws → Eqn
  q310 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 (lit c4))

-- T312-beta @14213243: 8 steps
lem-T312-beta-at14213243 : Ws → ⟪ (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at14213243 c4 = derive (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q307 c4) ∷
   rw 2 (q272 c4) ∷
   rw 3 (q307 c4) ∷
   rw 1 (q308 c4) ∷
   rw 0 (q309 c4) ∷
   rw⁻ 1 (q310 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 (lit c4))
  q312 : Ws → Eqn
  q312 c4 = eqn (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4)
  q313 : Ws → Eqn
  q313 c4 = eqn (Sw01 ∷ Bx0-4123 ∷ []) (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ (lit c4))
  q314 : Ws → Eqn
  q314 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4))

-- T312-beta @0114203243: 8 steps
lem-T312-beta-at0114203243 : Ws → ⟪ (Toff204 ∷ Bx1-4023 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0114203243 c4 = derive (Toff204 ∷ Bx1-4023 ∷ Toff204 ∷ []) (Bx1-4023 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q311 c4) ∷
   rw 2 (q274 c4) ∷
   rw 3 (q311 c4) ∷
   rw 1 (q312 c4) ∷
   rw 0 (q313 c4) ∷
   rw 1 (q314 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

private
  q315 : Ws → Eqn
  q315 c4 = eqn (Toff204 ∷ Bx1-4023 ∷ Toff204 ∷ []) (Bx1-4023 ∷ CCZ034 ∷ []) (lem-T312-beta-at0114203243 c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (Sw12 ∷ Bx1-4023 ∷ []) (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ (lit c4))

-- T312-beta @0214203143: 8 steps
lem-T312-beta-at0214203143 : Ws → ⟪ (Toff104 ∷ Bx2-4013 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0214203143 c4 = derive (Toff104 ∷ Bx2-4013 ∷ Toff104 ∷ []) (Bx2-4013 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q279 c4) ∷
   rw 2 (q277 c4) ∷
   rw 3 (q279 c4) ∷
   rw 1 (q315 c4) ∷
   rw 0 (q316 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q317 : Ws → Eqn
  q317 c4 = eqn (Sw23 ∷ Toff104 ∷ []) (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 (lit c4))
  q318 : Ws → Eqn
  q318 c4 = eqn (Toff104 ∷ Bx2-4013 ∷ Toff104 ∷ []) (Bx2-4013 ∷ CCZ034 ∷ []) (lem-T312-beta-at0214203143 c4)
  q319 : Ws → Eqn
  q319 c4 = eqn (Sw23 ∷ Bx2-4013 ∷ []) (Bx3-4012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4013⟩ (lit c4))

-- T312-beta @0314203142: 8 steps
lem-T312-beta-at0314203142 : Ws → ⟪ (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0314203142 c4 = derive (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q317 c4) ∷
   rw 2 (q281 c4) ∷
   rw 3 (q317 c4) ∷
   rw 1 (q318 c4) ∷
   rw 0 (q319 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

private
  q320 : Ws → Eqn
  q320 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4))
  q321 : Ws → Eqn
  q321 c4 = eqn (Sw12 ∷ Bx3-4021 ∷ []) (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ (lit c4))
  q322 : Ws → Eqn
  q322 c4 = eqn (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4)
  q323 : Ws → Eqn
  q323 c4 = eqn (Sw12 ∷ Bx3-4012 ∷ []) (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ (lit c4))

-- T312-beta @0314203241: 8 steps
lem-T312-beta-at0314203241 : Ws → ⟪ (Toff204 ∷ Bx3-4021 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at0314203241 c4 = derive (Toff204 ∷ Bx3-4021 ∷ Toff204 ∷ []) (Bx3-4021 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q320 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q320 c4) ∷
   rw 1 (q322 c4) ∷
   rw 0 (q323 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 (lit c4))
  q325 : Ws → Eqn
  q325 c4 = eqn (Sw01 ∷ Bx3-4120 ∷ []) (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ (lit c4))
  q326 : Ws → Eqn
  q326 c4 = eqn (Toff204 ∷ Bx3-4021 ∷ Toff204 ∷ []) (Bx3-4021 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314203241 c4)
  q327 : Ws → Eqn
  q327 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4))

-- T312-beta @0314213240: 8 steps
lem-T312-beta-at0314213240 : Ws → ⟪ (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at0314213240 c4 = derive (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q324 c4) ∷
   rw 2 (q325 c4) ∷
   rw 3 (q324 c4) ∷
   rw 1 (q326 c4) ∷
   rw 0 (q300 c4) ∷
   rw 1 (q327 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

-- sym34 @0314203241: 5 steps
lem-sym34-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym34-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-4012 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q321 c4) ∷
   rw 1 (q299 c4) ∷
   rw 0 (q321 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = eqn (Bx3-4021 ∷ []) (Bx3-4012 ∷ []) (lem-sym34-at0314203241 c4)
  q329 : Ws → Eqn
  q329 c4 = eqn (Sw01 ∷ Bx3-4012 ∷ []) (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ (lit c4))

-- sym34 @0314213240: 5 steps
lem-sym34-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym34-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Bx3-4102 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q325 c4) ∷
   rw 1 (q328 c4) ∷
   rw 0 (q329 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q330 : Ws → Eqn
  q330 c4 = eqn (Sw12 ∷ Bx0-1324 ∷ []) (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4))

-- sym23 @1221: 5 steps
lem-sym23-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym23-at1221 c4 = derive (Bx0-2134 ∷ []) (Bx0-2314 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 1 (q246 c4) ∷
   rw 0 (q330 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = eqn (Bx0-2134 ∷ []) (Bx0-2314 ∷ []) (lem-sym23-at1221 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (Sw23 ∷ Bx0-2314 ∷ []) (Bx0-3214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2314⟩ (lit c4))

-- sym23 @132132: 5 steps
lem-sym23-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym23-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-3214 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q270 c4) ∷
   rw 1 (q331 c4) ∷
   rw 0 (q332 c4) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

private
  q333 : Ws → Eqn
  q333 c4 = eqn (Bx0-3124 ∷ []) (Bx0-3214 ∷ []) (lem-sym23-at132132 c4)
  q334 : Ws → Eqn
  q334 c4 = eqn (Sw34 ∷ Bx0-3214 ∷ []) (Bx0-4213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3214⟩ (lit c4))

-- sym23 @14213243: 5 steps
lem-sym23-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym23-at14213243 c4 = derive (Bx0-4123 ∷ []) (Bx0-4213 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q272 c4) ∷
   rw 1 (q333 c4) ∷
   rw 0 (q334 c4) ∷
   rw 1 (q97 c4) ∷ []) Eq.refl

private
  q335 : Ws → Eqn
  q335 c4 = eqn (Bx0-4123 ∷ []) (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4)
  q336 : Ws → Eqn
  q336 c4 = eqn (Sw01 ∷ Bx0-4213 ∷ []) (Bx1-4203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4213⟩ (lit c4))

-- sym23 @0114203243: 5 steps
lem-sym23-at0114203243 : Ws → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ []) ⟫ʷ
lem-sym23-at0114203243 c4 = derive (Bx1-4023 ∷ []) (Bx1-4203 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q274 c4) ∷
   rw 1 (q335 c4) ∷
   rw 0 (q336 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q337 : Ws → Eqn
  q337 c4 = eqn (Bx1-4023 ∷ []) (Bx1-4203 ∷ []) (lem-sym23-at0114203243 c4)
  q338 : Ws → Eqn
  q338 c4 = eqn (Sw12 ∷ Bx1-4203 ∷ []) (Bx2-4103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4203⟩ (lit c4))

-- sym23 @0214203143: 5 steps
lem-sym23-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym23-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q277 c4) ∷
   rw 1 (q337 c4) ∷
   rw 0 (q338 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q339 : Ws → Eqn
  q339 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4)
  q340 : Ws → Eqn
  q340 c4 = eqn (Sw23 ∷ Bx2-4103 ∷ []) (Bx3-4102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4103⟩ (lit c4))

-- sym23 @0314203142: 5 steps
lem-sym23-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym23-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-4102 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q281 c4) ∷
   rw 1 (q339 c4) ∷
   rw 0 (q340 c4) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = eqn (Bx3-4012 ∷ []) (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4)

-- sym23 @0314213042: 5 steps
lem-sym23-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym23-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q284 c4) ∷
   rw 1 (q341 c4) ∷
   rw 0 (q284 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q342 : Ws → Eqn
  q342 c4 = eqn (Bx0-1234 ∷ []) (Bx0-2134 ∷ []) (lem-sym12 c4)

-- sym12 @1221: 5 steps
lem-sym12-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym12-at1221 c4 = derive (Bx0-2134 ∷ []) (Bx0-1234 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 1 (q342 c4) ∷
   rw 0 (q90 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym12-at1221 c4)
  q344 : Ws → Eqn
  q344 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4))

-- sym12 @132132: 5 steps
lem-sym12-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym12-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-1324 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q270 c4) ∷
   rw 1 (q343 c4) ∷
   rw 0 (q344 c4) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

private
  q345 : Ws → Eqn
  q345 c4 = eqn (Bx0-3124 ∷ []) (Bx0-1324 ∷ []) (lem-sym12-at132132 c4)
  q346 : Ws → Eqn
  q346 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4))

-- sym12 @14213243: 5 steps
lem-sym12-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym12-at14213243 c4 = derive (Bx0-4123 ∷ []) (Bx0-1423 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q272 c4) ∷
   rw 1 (q345 c4) ∷
   rw 0 (q346 c4) ∷
   rw 1 (q97 c4) ∷ []) Eq.refl

private
  q347 : Ws → Eqn
  q347 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4)
  q348 : Ws → Eqn
  q348 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4))

-- sym12 @0114203243: 5 steps
lem-sym12-at0114203243 : Ws → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym12-at0114203243 c4 = derive (Bx1-4023 ∷ []) (Bx1-0423 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q274 c4) ∷
   rw 1 (q347 c4) ∷
   rw 0 (q348 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q349 : Ws → Eqn
  q349 c4 = eqn (Bx1-4023 ∷ []) (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4)
  q350 : Ws → Eqn
  q350 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4))

-- sym12 @0214203143: 5 steps
lem-sym12-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym12-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-0413 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q277 c4) ∷
   rw 1 (q349 c4) ∷
   rw 0 (q350 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q351 : Ws → Eqn
  q351 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4)
  q352 : Ws → Eqn
  q352 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4))

-- sym12 @0314203142: 5 steps
lem-sym12-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym12-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-0412 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q281 c4) ∷
   rw 1 (q351 c4) ∷
   rw 0 (q352 c4) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

-- beta-inv @2332: 5 steps
lem-beta-inv-at2332 : Ws → ⟪ (Bx0-1324 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at2332 c4 = derive (Bx0-1324 ∷ Bx0-1324 ∷ []) []
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 2 (q114 c4) ∷
   rw 1 (q177 c4) ∷
   rw 0 (q113 c4) ∷ []) Eq.refl

private
  q353 : Ws → Eqn
  q353 c4 = eqn (Bx0-1324 ∷ Bx0-1324 ∷ []) [] (lem-beta-inv-at2332 c4)

-- beta-inv @243243: 5 steps
lem-beta-inv-at243243 : Ws → ⟪ (Bx0-1423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at243243 c4 = derive (Bx0-1423 ∷ Bx0-1423 ∷ []) []
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q117 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q353 c4) ∷
   rw 0 (q97 c4) ∷ []) Eq.refl

private
  q354 : Ws → Eqn
  q354 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4))
  q355 : Ws → Eqn
  q355 c4 = eqn (Bx0-1423 ∷ Bx0-1423 ∷ []) [] (lem-beta-inv-at243243 c4)

-- beta-inv @0110243243: 5 steps
lem-beta-inv-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0110243243 c4 = derive (Bx1-0423 ∷ Bx1-0423 ∷ []) []
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q354 c4) ∷
   rw 2 (q354 c4) ∷
   rw 1 (q355 c4) ∷
   rw 0 (q194 c4) ∷ []) Eq.refl

private
  q356 : Ws → Eqn
  q356 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4))
  q357 : Ws → Eqn
  q357 c4 = eqn (Bx1-0423 ∷ Bx1-0423 ∷ []) [] (lem-beta-inv-at0110243243 c4)

-- beta-inv @0210243143: 5 steps
lem-beta-inv-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0210243143 c4 = derive (Bx2-0413 ∷ Bx2-0413 ∷ []) []
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q356 c4) ∷
   rw 2 (q356 c4) ∷
   rw 1 (q357 c4) ∷
   rw 0 (q89 c4) ∷ []) Eq.refl

private
  q358 : Ws → Eqn
  q358 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4))
  q359 : Ws → Eqn
  q359 c4 = eqn (Bx2-0413 ∷ Bx2-0413 ∷ []) [] (lem-beta-inv-at0210243143 c4)

-- beta-inv @0310243142: 5 steps
lem-beta-inv-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0310243142 c4 = derive (Bx3-0412 ∷ Bx3-0412 ∷ []) []
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q358 c4) ∷
   rw 2 (q358 c4) ∷
   rw 1 (q359 c4) ∷
   rw 0 (q113 c4) ∷ []) Eq.refl

private
  q360 : Ws → Eqn
  q360 c4 = eqn (Sw01 ∷ Bx2-4103 ∷ []) (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ (lit c4))

-- beta-T @0214213043: 8 steps
lem-beta-T-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q360 c4) ∷
   rw 1 (q282 c4) ∷
   rw 0 (q311 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 2 (q311 c4) ∷
   rw⁻ 3 (q221 c4) ∷
   rw 4 (q194 c4) ∷ []) Eq.refl

-- sym23 @0214213043: 5 steps
lem-sym23-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym23-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Bx2-4013 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q360 c4) ∷
   rw 1 (q339 c4) ∷
   rw 0 (q360 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q361 : Ws → Eqn
  q361 c4 = eqn (CCZ023 ∷ []) (CCZ023 ∷ []) (wl0242 (lit c4))
  q362 : Ws → Eqn
  q362 c4 = eqn (CCZ023 ∷ CCZ023 ∷ []) [] (wl0243 (lit c4))
  q363 : Ws → Eqn
  q363 c4 = eqn (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-beta-T-at0314213042 c4)
  q364 : Ws → Eqn
  q364 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4)
  q365 : Ws → Eqn
  q365 c4 = eqn (Toff214 ∷ Toff214 ∷ []) [] (wl0244 (lit c4))
  q366 : Ws → Eqn
  q366 c4 = eqn (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4)
  q367 : Ws → Eqn
  q367 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4)
  q368 : Ws → Eqn
  q368 c4 = eqn (Bx3-4102 ∷ []) (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4)
  q369 : Ws → Eqn
  q369 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4)
  q370 : Ws → Eqn
  q370 c4 = eqn (Bx3-0412 ∷ Bx3-0412 ∷ []) [] (lem-beta-inv-at0310243142 c4)
  q371 : Ws → Eqn
  q371 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0055 c4)
  q372 : Ws → Eqn
  q372 c4 = eqn (Bx2-4103 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-beta-T-at0214213043 c4)
  q373 : Ws → Eqn
  q373 c4 = eqn (Bx2-4103 ∷ []) (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4)

-- F0-D: 15 steps
lem-F0-D : Ws → ⟪ (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-F0-D c4 = derive (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (Bx2-0413 ∷ [])
  (rw 4 (q361 c4) ∷
   rw⁻ 6 (q362 c4) ∷
   rw⁻ 3 (q363 c4) ∷
   rw 3 (q364 c4) ∷
   rw⁻ 4 (q365 c4) ∷
   rw 2 (q366 c4) ∷
   rw 2 (q367 c4) ∷
   rw 2 (q368 c4) ∷
   rw 2 (q369 c4) ∷
   rw 1 (q370 c4) ∷
   rw 0 (q371 c4) ∷
   rw 1 (q361 c4) ∷
   rw⁻ 0 (q372 c4) ∷
   rw 0 (q373 c4) ∷
   rw 0 (q351 c4) ∷ []) Eq.refl

private
  q374 : Ws → Eqn
  q374 c4 = eqn (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4))
  q375 : Ws → Eqn
  q375 c4 = eqn (Sw01 ∷ Bx0-1243 ∷ []) (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ (lit c4))

-- sym34 @0110: 5 steps
lem-sym34-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym34-at0110 c4 = derive (Bx1-0234 ∷ []) (Bx1-0243 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q374 c4) ∷
   rw 1 (q287 c4) ∷
   rw 0 (q375 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q376 : Ws → Eqn
  q376 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4))
  q377 : Ws → Eqn
  q377 c4 = eqn (Bx1-0234 ∷ []) (Bx1-0243 ∷ []) (lem-sym34-at0110 c4)
  q378 : Ws → Eqn
  q378 c4 = eqn (Sw12 ∷ Bx1-0243 ∷ []) (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ (lit c4))

-- sym34 @021021: 5 steps
lem-sym34-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym34-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-0143 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q376 c4) ∷
   rw 1 (q377 c4) ∷
   rw 0 (q378 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q379 : Ws → Eqn
  q379 c4 = eqn (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4))
  q380 : Ws → Eqn
  q380 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0143 ∷ []) (lem-sym34-at021021 c4)
  q381 : Ws → Eqn
  q381 c4 = eqn (Sw23 ∷ Bx2-0143 ∷ []) (Bx3-0142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0143⟩ (lit c4))

-- sym34 @03102132: 5 steps
lem-sym34-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym34-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-0142 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q379 c4) ∷
   rw 1 (q380 c4) ∷
   rw 0 (q381 c4) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

private
  q382 : Ws → Eqn
  q382 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4))
  q383 : Ws → Eqn
  q383 c4 = eqn (Sw34 ∷ Bx0-1234 ∷ []) (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4))
  q384 : Ws → Eqn
  q384 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4))

-- c124-beta @3443: 7 steps
lem-c124-beta-at3443 : Ws → ⟪ (CCZ123 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-c124-beta-at3443 c4 = derive (CCZ123 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q382 c4) ∷
   rw 2 (q98 c4) ∷
   rw 1 (q169 c4) ∷
   rw 0 (q383 c4) ∷
   rw 1 (q384 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q385 : Ws → Eqn
  q385 c4 = eqn (Sw01 ∷ Bx1-0243 ∷ []) (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4))
  q386 : Ws → Eqn
  q386 c4 = eqn (CCZ123 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ []) (lem-c124-beta-at3443 c4)

-- c124-beta @01103443: 7 steps
lem-c124-beta-at01103443 : Ws → ⟪ (CCZ023 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ CCZ023 ∷ []) ⟫ʷ
lem-c124-beta-at01103443 c4 = derive (CCZ023 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q223 c4) ∷
   rw 2 (q385 c4) ∷
   rw 1 (q386 c4) ∷
   rw 0 (q375 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

private
  q387 : Ws → Eqn
  q387 c4 = eqn (Sw12 ∷ Bx2-0143 ∷ []) (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4))
  q388 : Ws → Eqn
  q388 c4 = eqn (CCZ023 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ CCZ023 ∷ []) (lem-c124-beta-at01103443 c4)

-- c124-beta @0210213443: 7 steps
lem-c124-beta-at0210213443 : Ws → ⟪ (CCZ013 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ013 ∷ []) ⟫ʷ
lem-c124-beta-at0210213443 c4 = derive (CCZ013 ∷ Bx2-0143 ∷ []) (Bx2-0143 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q220 c4) ∷
   rw 2 (q387 c4) ∷
   rw 1 (q388 c4) ∷
   rw 0 (q378 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q389 : Ws → Eqn
  q389 c4 = eqn (Sw23 ∷ Bx3-0142 ∷ []) (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4))
  q390 : Ws → Eqn
  q390 c4 = eqn (CCZ013 ∷ Bx2-0143 ∷ []) (Bx2-0143 ∷ CCZ013 ∷ []) (lem-c124-beta-at0210213443 c4)

-- c124-beta @0310213442: 7 steps
lem-c124-beta-at0310213442 : Ws → ⟪ (CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at0310213442 c4 = derive (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q389 c4) ∷
   rw 1 (q390 c4) ∷
   rw 0 (q381 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

-- sym34 @3443: 5 steps
lem-sym34-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym34-at3443 c4 = derive (Bx0-1243 ∷ []) (Bx0-1234 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 1 (q287 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q97 c4) ∷ []) Eq.refl

private
  q391 : Ws → Eqn
  q391 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1234 ∷ []) (lem-sym34-at3443 c4)
  q392 : Ws → Eqn
  q392 c4 = eqn (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4))

-- sym34 @01103443: 5 steps
lem-sym34-at01103443 : Ws → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym34-at01103443 c4 = derive (Bx1-0243 ∷ []) (Bx1-0234 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q385 c4) ∷
   rw 1 (q391 c4) ∷
   rw 0 (q392 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q393 : Ws → Eqn
  q393 c4 = eqn (Bx1-0243 ∷ []) (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4)
  q394 : Ws → Eqn
  q394 c4 = eqn (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4))

-- sym34 @0210213443: 5 steps
lem-sym34-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym34-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Bx2-0134 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q387 c4) ∷
   rw 1 (q393 c4) ∷
   rw 0 (q394 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl

private
  q395 : Ws → Eqn
  q395 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4)
  q396 : Ws → Eqn
  q396 c4 = eqn (Sw23 ∷ Bx2-0134 ∷ []) (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4))

-- sym34 @0310213442: 5 steps
lem-sym34-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym34-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-0124 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q389 c4) ∷
   rw 1 (q395 c4) ∷
   rw 0 (q396 c4) ∷
   rw 1 (q113 c4) ∷ []) Eq.refl

private
  q397 : Ws → Eqn
  q397 c4 = eqn (Bx3-0124 ∷ []) (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4)
  q398 : Ws → Eqn
  q398 c4 = eqn (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4)
  q399 : Ws → Eqn
  q399 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4)

-- auto CCZ012 | BOX(3;0124): 3 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩ : Ws → ⟪ (CCZ012 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩ c4 = derive (CCZ012 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ CCZ012 ∷ [])
  (rw 1 (q397 c4) ∷
   rw 0 (q398 c4) ∷
   rw 0 (q399 c4) ∷ []) Eq.refl

private
  q400 : Ws → Eqn
  q400 c4 = eqn (Sw12 ∷ Bx3-0214 ∷ []) (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4))
  q401 : Ws → Eqn
  q401 c4 = eqn (CCZ012 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩ c4)
  q402 : Ws → Eqn
  q402 c4 = eqn (Sw12 ∷ Bx3-0124 ∷ []) (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ (lit c4))

-- auto CCZ012 | BOX(3;0124) @1221: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 c4 = derive (CCZ012 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw 2 (q400 c4) ∷
   rw 1 (q401 c4) ∷
   rw 0 (q402 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q403 : Ws → Eqn
  q403 c4 = eqn (Sw23 ∷ Bx2-0314 ∷ []) (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ (lit c4))
  q404 : Ws → Eqn
  q404 c4 = eqn (CCZ012 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 c4)
  q405 : Ws → Eqn
  q405 c4 = eqn (Sw23 ∷ Bx3-0214 ∷ []) (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ (lit c4))

-- auto CCZ012 | BOX(3;0124) @132132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 c4 = derive (CCZ013 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q403 c4) ∷
   rw 1 (q404 c4) ∷
   rw 0 (q405 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

private
  q406 : Ws → Eqn
  q406 c4 = eqn (Sw34 ∷ Bx2-0413 ∷ []) (Bx2-0314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0413⟩ (lit c4))
  q407 : Ws → Eqn
  q407 c4 = eqn (CCZ013 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 c4)
  q408 : Ws → Eqn
  q408 c4 = eqn (Sw34 ∷ Bx2-0314 ∷ []) (Bx2-0413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0314⟩ (lit c4))

-- auto CCZ012 | BOX(3;0124) @14213243: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 : Ws → ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 c4 = derive (CCZ014 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q406 c4) ∷
   rw 1 (q407 c4) ∷
   rw 0 (q408 c4) ∷
   rw 1 (q231 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q409 : Ws → Eqn
  q409 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 (lit c4))
  q410 : Ws → Eqn
  q410 c4 = eqn (CCZ014 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 c4)

-- auto CCZ012 | BOX(3;0124) @142142: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 : Ws → ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 c4 = derive (CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q113 c4) ∷
   rw 1 (q409 c4) ∷
   rw 2 (q358 c4) ∷
   rw 1 (q410 c4) ∷
   rw 0 (q352 c4) ∷
   rw 1 (q409 c4) ∷
   rw 2 (q113 c4) ∷ []) Eq.refl

private
  q411 : Ws → Eqn
  q411 c4 = eqn (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (Bx2-0413 ∷ []) (lem-F0-D c4)
  q412 : Ws → Eqn
  q412 c4 = eqn (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (lem-F0-B c4)
  q413 : Ws → Eqn
  q413 c4 = eqn (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (lem-F0-C c4)
  q414 : Ws → Eqn
  q414 c4 = eqn (CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (wp0056 c4)
  q415 : Ws → Eqn
  q415 c4 = eqn (CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 c4)
  q416 : Ws → Eqn
  q416 c4 = eqn (CCZ014 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ []) (wp0057 c4)

-- F0: 13 steps
lem-F0 : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F0 c4 = derive (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ [])
  (re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q411 c4) ∷
   rw 2 (q412 c4) ∷
   rw 2 (q413 c4) ∷
   rw⁻ 6 (q414 c4) ∷
   rw 0 (q415 c4) ∷
   rw 1 (q416 c4) ∷
   rw 5 (q371 c4) ∷
   re 2 1 (Sb3-0-2-1 ∷ []) ∷
   re 4 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 0 5 (Sb3-0-41-2 ∷ []) ∷ []) Eq.refl

private
  q417 : Ws → Eqn
  q417 c4 = eqn (Toff304 ∷ Toff304 ∷ []) [] (wp0058 c4)
  q418 : Ws → Eqn
  q418 c4 = eqn (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) [] (wl0245 (lit c4))
  q419 : Ws → Eqn
  q419 c4 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wl0246 (lit c4))
  q420 : Ws → Eqn
  q420 c4 = eqn (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ []) (lem-F0 c4)
  q421 : Ws → Eqn
  q421 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0059 c4)
  q422 : Ws → Eqn
  q422 c4 = eqn (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] (wl0247 (lit c4))
  q423 : Ws → Eqn
  q423 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q424 : Ws → Eqn
  q424 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl0249 (lit c4))
  q425 : Ws → Eqn
  q425 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl0250 (lit c4))

-- F0d: 61 steps
lem-F0d : Ws → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-41-2 ∷ []) ⟫ʷ
lem-F0d c4 = derive (Sb⁻2-0-41-3 ∷ []) (Sb⁻3-0-41-2 ∷ [])
  (rw⁻ 1 (q88 c4) ∷
   rw⁻ 2 (q417 c4) ∷
   rw⁻ 3 (q418 c4) ∷
   re 5 1 (Bx3-02 ∷ []) ∷
   re 8 1 (Bx3-02 ∷ []) ∷
   re 3 6 (Bx0-312 ∷ []) ∷
   re 4 1 (Bx⁻3-02 ∷ []) ∷
   re 7 1 (Bx⁻3-02 ∷ []) ∷
   re 4 6 (Bx⁻0-312 ∷ []) ∷
   rw⁻ 4 (q417 c4) ∷
   rw⁻ 5 (q88 c4) ∷
   rw⁻ 6 (q418 c4) ∷
   re 8 1 (Bx3-02 ∷ []) ∷
   re 11 1 (Bx3-02 ∷ []) ∷
   re 6 6 (Bx0-312 ∷ []) ∷
   re 7 1 (Bx⁻3-02 ∷ []) ∷
   re 10 1 (Bx⁻3-02 ∷ []) ∷
   re 7 6 (Bx⁻0-312 ∷ []) ∷
   re 1 6 (Bx3-0412 ∷ []) ∷
   re 2 6 (Bx⁻3-0412 ∷ []) ∷
   rw⁻ 2 (q365 c4) ∷
   rw⁻ 3 (q419 c4) ∷
   re 3 1 (Sb3-0-2-1 ∷ []) ∷
   re 4 1 (Sb⁻3-0-2-1 ∷ []) ∷
   rw⁻ 4 (q365 c4) ∷
   rw⁻ 5 (q77 c4) ∷
   re 5 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 6 1 (Sb3-0-2-1 ∷ []) ∷
   re 1 5 (Sb3-0-41-2 ∷ []) ∷
   re 2 5 (Sb⁻3-0-41-2 ∷ []) ∷
   rw⁻ 1 (q420 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   rw 9 (q141 c4) ∷
   rw 8 (q421 c4) ∷
   re 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   re 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 15 1 (CZ03 ∷ []) ∷
   re 18 1 (CZ03 ∷ []) ∷
   rw 7 (q422 c4) ∷
   rw 6 (q421 c4) ∷
   rw 5 (q141 c4) ∷
   re 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 12 1 (CZ03 ∷ []) ∷
   re 15 1 (CZ03 ∷ []) ∷
   rw 4 (q422 c4) ∷
   rw 3 (q423 c4) ∷
   re 2 1 (CS03⁻ ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw 2 (q424 c4) ∷
   rw 1 (q423 c4) ∷
   re 0 1 (CS03 ∷ []) ∷
   re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q425 c4) ∷ []) Eq.refl

private
  q426 : Ws → Eqn
  q426 c4 = eqn (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4))

-- sym12 @011220: 5 steps
lem-sym12-at011220 : Ws → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym12-at011220 c4 = derive (Bx1-2034 ∷ []) (Bx1-0234 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q426 c4) ∷
   rw 1 (q343 c4) ∷
   rw 0 (q392 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q427 : Ws → Eqn
  q427 c4 = eqn (CX10 ∷ Sw01 ∷ []) (Sw01 ∷ CX01 ∷ []) (wl0070 (lit c4))
  q428 : Ws → Eqn
  q428 c4 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wl0251 (lit c4))

-- CX10-beta-c @0110: 7 steps
lem-CX10-beta-c-at0110 : Ws → ⟪ (CX01 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CX01 ∷ []) ⟫ʷ
lem-CX10-beta-c-at0110 c4 = derive (CX01 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CX01 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q427 c4) ∷
   rw 2 (q374 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q392 c4) ∷
   rw⁻ 1 (q428 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl

private
  q429 : Ws → Eqn
  q429 c4 = eqn (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4))

-- sym12 @0110: 5 steps
lem-sym12-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ []) ⟫ʷ
lem-sym12-at0110 c4 = derive (Bx1-0234 ∷ []) (Bx1-2034 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw 1 (q374 c4) ∷
   rw 1 (q342 c4) ∷
   rw 0 (q429 c4) ∷
   rw 1 (q194 c4) ∷ []) Eq.refl

private
  q430 : Ws → Eqn
  q430 c4 = eqn (Bx1-2034 ∷ []) (Bx1-0234 ∷ []) (lem-sym12-at011220 c4)
  q431 : Ws → Eqn
  q431 c4 = eqn (CX01 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CX01 ∷ []) (lem-CX10-beta-c-at0110 c4)
  q432 : Ws → Eqn
  q432 c4 = eqn (Bx1-0234 ∷ []) (Bx1-2034 ∷ []) (lem-sym12-at0110 c4)

-- auto CX01 | BOX(1;2034): 3 steps
lem-auto-CX01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CX01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOX⟨1·2034⟩ c4 = derive (CX01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CX01 ∷ [])
  (rw 1 (q430 c4) ∷
   rw 0 (q431 c4) ∷
   rw 0 (q432 c4) ∷ []) Eq.refl

private
  q433 : Ws → Eqn
  q433 c4 = eqn (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 (lit c4))
  q434 : Ws → Eqn
  q434 c4 = eqn (CZ02 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ []) (lem-CZ10-beta-c c4)
  q435 : Ws → Eqn
  q435 c4 = eqn (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 (lit c4))

-- CZ10-beta-c @1221: 7 steps
lem-CZ10-beta-c-at1221 : Ws → ⟪ (CZ01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZ10-beta-c-at1221 c4 = derive (CZ01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CZ01 ∷ [])
  (rw⁻ 0 (q89 c4) ∷
   rw 1 (q433 c4) ∷
   rw 2 (q90 c4) ∷
   rw 1 (q434 c4) ∷
   rw 0 (q303 c4) ∷
   rw 1 (q435 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q436 : Ws → Eqn
  q436 c4 = eqn (CZ01 ∷ Sw01 ∷ []) (Sw01 ∷ CZ01 ∷ []) (wl0130 (lit c4))
  q437 : Ws → Eqn
  q437 c4 = eqn (CZ01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CZ01 ∷ []) (lem-CZ10-beta-c-at1221 c4)

-- CZ10-beta-c @011220: 7 steps
lem-CZ10-beta-c-at011220 : Ws → ⟪ (CZ01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZ10-beta-c-at011220 c4 = derive (CZ01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ [])
  (rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q436 c4) ∷
   rw 2 (q426 c4) ∷
   rw 1 (q437 c4) ∷
   rw 0 (q429 c4) ∷
   rw⁻ 1 (q436 c4) ∷
   rw 2 (q194 c4) ∷ []) Eq.refl
