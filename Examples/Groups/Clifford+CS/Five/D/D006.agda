{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD006 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D006 (Sᴰ : SD006) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-TOFF034 ; lem-comm-CSd12-TOFF034 ; lem-comm-CZ04-CCZ123 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ23-CCZ014 ; lem-comm-CZ24-CCZ013 ; lem-comm-TOFF034-CSd12 ; lem-comm-TOFF301-CSd24 ; lem-comm-TOFF401-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-TOFF401 ; lem-comm-CS24-TOFF301 ; lem-comm-CSd23-TOFF401 ; lem-comm-CSd24-TOFF301 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ24-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-SWAP03-BOX⟨2·14⟩)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-tQ-at0213243140 : Ws → St 23
  lem-box-tQ-at0213243140 = pickᴰ 0 Sᴰ
  lem-box-tQ-at0220 : Ws → St 24
  lem-box-tQ-at0220 = pickᴰ 1 Sᴰ
  lem-box-tQ-at032032 : Ws → St 25
  lem-box-tQ-at032032 = pickᴰ 2 Sᴰ
  lem-box-tQ-at04203243 : Ws → St 26
  lem-box-tQ-at04203243 = pickᴰ 3 Sᴰ
  lem-box-tQ-at13243142 : Ws → St 27
  lem-box-tQ-at13243142 = pickᴰ 4 Sᴰ
  lem-box-tQ-at13243241 : Ws → St 28
  lem-box-tQ-at13243241 = pickᴰ 5 Sᴰ
  lem-box-tQ-at14233142 : Ws → St 29
  lem-box-tQ-at14233142 = pickᴰ 6 Sᴰ
  lem-box-tQ-at14233241 : Ws → St 30
  lem-box-tQ-at14233241 = pickᴰ 7 Sᴰ
  lem-cQ : Ws → St 31
  lem-cQ = pickᴰ 8 Sᴰ
  lem-cQ-at0110 : Ws → St 32
  lem-cQ-at0110 = pickᴰ 9 Sᴰ
  lem-cQ-at0210233441 : Ws → St 33
  lem-cQ-at0210233441 = pickᴰ 10 Sᴰ
  lem-cQ-at0210243143 : Ws → St 34
  lem-cQ-at0210243143 = pickᴰ 11 Sᴰ
  lem-cQ-at0213203441 : Ws → St 35
  lem-cQ-at0213203441 = pickᴰ 12 Sᴰ
  lem-cQ-at0214203143 : Ws → St 36
  lem-cQ-at0214203143 = pickᴰ 13 Sᴰ
  lem-cQ-at0214213043 : Ws → St 37
  lem-cQ-at0214213043 = pickᴰ 14 Sᴰ
  lem-cQ-at022330 : Ws → St 38
  lem-cQ-at022330 = pickᴰ 15 Sᴰ
  lem-cQ-at0310243142 : Ws → St 39
  lem-cQ-at0310243142 = pickᴰ 16 Sᴰ
  lem-cQ-at0312213440 : Ws → St 40
  lem-cQ-at0312213440 = pickᴰ 17 Sᴰ
  lem-cQ-at0312243140 : Ws → St 41
  lem-cQ-at0312243140 = pickᴰ 18 Sᴰ
  lem-cQ-at0314203142 : Ws → St 42
  lem-cQ-at0314203142 = pickᴰ 19 Sᴰ
  lem-cQ-at0314213042 : Ws → St 43
  lem-cQ-at0314213042 = pickᴰ 20 Sᴰ
  lem-cQ-at0330 : Ws → St 44
  lem-cQ-at0330 = pickᴰ 21 Sᴰ
  lem-cQ-at033440 : Ws → St 45
  lem-cQ-at033440 = pickᴰ 22 Sᴰ
  lem-cQ-at043043 : Ws → St 46
  lem-cQ-at043043 = pickᴰ 23 Sᴰ
  lem-cQ-at1221 : Ws → St 47
  lem-cQ-at1221 = pickᴰ 24 Sᴰ
  lem-cQ-at12213443 : Ws → St 48
  lem-cQ-at12213443 = pickᴰ 25 Sᴰ
  lem-cQ-at122331 : Ws → St 49
  lem-cQ-at122331 = pickᴰ 26 Sᴰ
  lem-cQ-at12233441 : Ws → St 50
  lem-cQ-at12233441 = pickᴰ 27 Sᴰ
  lem-cQ-at12243143 : Ws → St 51
  lem-cQ-at12243143 = pickᴰ 28 Sᴰ
  lem-cQ-at122441 : Ws → St 52
  lem-cQ-at122441 = pickᴰ 29 Sᴰ
  lem-cQ-at132132 : Ws → St 53
  lem-cQ-at132132 = pickᴰ 30 Sᴰ
  lem-cQ-at13213442 : Ws → St 54
  lem-cQ-at13213442 = pickᴰ 31 Sᴰ
  lem-cQ-at1331 : Ws → St 55
  lem-cQ-at1331 = pickᴰ 32 Sᴰ
  lem-cQ-at133441 : Ws → St 56
  lem-cQ-at133441 = pickᴰ 33 Sᴰ
  lem-cQ-at14213243 : Ws → St 57
  lem-cQ-at14213243 = pickᴰ 34 Sᴰ
  lem-cQ-at143143 : Ws → St 58
  lem-cQ-at143143 = pickᴰ 35 Sᴰ
  lem-cQ-at1441 : Ws → St 59
  lem-cQ-at1441 = pickᴰ 36 Sᴰ
  lem-cQ-at2332 : Ws → St 60
  lem-cQ-at2332 = pickᴰ 37 Sᴰ
  lem-cQ-at233442 : Ws → St 61
  lem-cQ-at233442 = pickᴰ 38 Sᴰ
  lem-cQ-at243243 : Ws → St 62
  lem-cQ-at243243 = pickᴰ 39 Sᴰ
  lem-cQ-at2442 : Ws → St 63
  lem-cQ-at2442 = pickᴰ 40 Sᴰ
  lem-cQ-at3443 : Ws → St 64
  lem-cQ-at3443 = pickᴰ 41 Sᴰ
  lem-tP-at021021 : Ws → St 65
  lem-tP-at021021 = pickᴰ 42 Sᴰ
  lem-tP-at0210213443 : Ws → St 66
  lem-tP-at0210213443 = pickᴰ 43 Sᴰ
  lem-tP-at0220 : Ws → St 67
  lem-tP-at0220 = pickᴰ 44 Sᴰ
  lem-tP-at03102132 : Ws → St 68
  lem-tP-at03102132 = pickᴰ 45 Sᴰ
  lem-tP-at032032 : Ws → St 69
  lem-tP-at032032 = pickᴰ 46 Sᴰ
  lem-tP-at0410213243 : Ws → St 70
  lem-tP-at0410213243 = pickᴰ 47 Sᴰ
  lem-tP-at04203243 : Ws → St 71
  lem-tP-at04203243 = pickᴰ 48 Sᴰ
  lem-tP-at13243142 : Ws → St 72
  lem-tP-at13243142 = pickᴰ 49 Sᴰ
  lem-tP-at13243241 : Ws → St 73
  lem-tP-at13243241 = pickᴰ 50 Sᴰ
  lem-tP-at14233142 : Ws → St 74
  lem-tP-at14233142 = pickᴰ 51 Sᴰ
  lem-tP-at14233241 : Ws → St 75
  lem-tP-at14233241 = pickᴰ 52 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 156 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 4 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 157 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 31 (lem-cQ c4)

-- tP: 7 steps
lem-tP : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP c4 = derive (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = wpE 8 c4
  q6 : Ws → Eqn
  q6 c4 = wlE 160 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = wlE 161 (lit c4)

-- box-tQ: 13 steps
lem-box-tQ : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ c4 = derive (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q5 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q4 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = wpE 14 c4
  q10 : Ws → Eqn
  q10 c4 = wlE 174 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 175 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = sE 34 (lem-cQ-at0210243143 c4)

-- tP @0210243143: 7 steps
lem-tP-at0210243143 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at0210243143 c4 = derive (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = wlE 182 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wpE 25 c4
  q15 : Ws → Eqn
  q15 c4 = eqn (CZ04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = wpE 26 c4

-- box-tQ @0210243143: 13 steps
lem-box-tQ-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q13 c4) ∷
   re 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw 0 (q14 c4) ∷
   rw 2 (q15 c4) ∷
   rw 1 (q12 c4) ∷
   rw 2 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = wpE 49 c4
  q18 : Ws → Eqn
  q18 c4 = wlE 200 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = sE 62 (lem-cQ-at243243 c4)

-- tP @243243: 7 steps
lem-tP-at243243 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at243243 c4 = derive (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q17 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = wlE 205 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 56 c4
  q22 : Ws → Eqn
  q22 c4 = eqn (CZ14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = wpE 57 c4

-- box-tQ @243243: 13 steps
lem-box-tQ-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at243243 c4 = derive (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q20 c4) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q23 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = wpE 78 c4
  q25 : Ws → Eqn
  q25 c4 = wlE 226 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = sE 52 (lem-cQ-at122441 c4)

-- tP @122441: 7 steps
lem-tP-at122441 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at122441 c4 = derive (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = wlE 231 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 83 c4
  q29 : Ws → Eqn
  q29 c4 = eqn (CZ24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = wpE 84 c4

-- box-tQ @122441: 13 steps
lem-box-tQ-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at122441 c4 = derive (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 0 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q26 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = wpE 111 c4
  q32 : Ws → Eqn
  q32 c4 = sE 47 (lem-cQ-at1221 c4)

-- box-tQ @1221: 13 steps
lem-box-tQ-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at1221 c4 = derive (Bx0-2134 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q31 c4) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q31 c4) ∷
   rw 0 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

-- tP @1221: 7 steps
lem-tP-at1221 : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at1221 c4 = derive (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q32 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = wpE 130 c4
  q34 : Ws → Eqn
  q34 c4 = wlE 290 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CZ13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = sE 60 (lem-cQ-at2332 c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 291 (lit c4)

-- box-tQ @2332: 13 steps
lem-box-tQ-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at2332 c4 = derive (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q33 c4) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q33 c4) ∷
   rw 0 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw 2 (q37 c4) ∷ []) Eq.refl

-- tP @2332: 7 steps
lem-tP-at2332 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at2332 c4 = derive (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = wlE 292 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = sE 51 (lem-cQ-at12243143 c4)

-- box-tQ @12243143: 13 steps
lem-box-tQ-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at12243143 c4 = derive (Bx0-2413 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw 2 (q38 c4) ∷
   re 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw 5 (q38 c4) ∷
   rw 0 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = sE 27 (lem-box-tQ-at13243142 c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 137 c4
  q42 : Ws → Eqn
  q42 c4 = wpE 138 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 139 c4
  q44 : Ws → Eqn
  q44 c4 = wlE 293 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 294 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q47 : Ws → Eqn
  q47 c4 = wpE 140 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 141 c4
  q49 : Ws → Eqn
  q49 c4 = wpE 142 c4
  q50 : Ws → Eqn
  q50 c4 = wpE 143 c4
  q51 : Ws → Eqn
  q51 c4 = wlE 295 (lit c4)

-- CXbc-box @13243142: 17 steps
lem-CXbc-box-at13243142 : Ws → ⟪ (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at13243142 c4 = derive (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) (Bx0-3412 ∷ CCZ234 ∷ [])
  (rw 1 (q40 c4) ∷
   rw 0 (q41 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 3 (q43 c4) ∷
   rw 2 (q41 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 9 (q45 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw⁻ 7 (q47 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   rw⁻ 6 (q44 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw 4 (q50 c4) ∷
   rw⁻ 0 (q40 c4) ∷
   rw⁻ 1 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = wpE 144 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 296 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 145 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 297 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 146 c4
  q57 : Ws → Eqn
  q57 c4 = wpE 147 c4
  q58 : Ws → Eqn
  q58 c4 = eqn (CS12⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS12 ∷ Toff034 ∷ []) (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = wpE 97 c4
  q61 : Ws → Eqn
  q61 c4 = wpE 148 c4
  q62 : Ws → Eqn
  q62 c4 = wlE 298 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wlE 299 (lit c4)

-- CXcb-box @13243142: 18 steps
lem-CXcb-box-at13243142 : Ws → ⟪ (CX14 ∷ Bx0-3412 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at13243142 c4 = derive (CX14 ∷ Bx0-3412 ∷ CX14 ∷ []) (Bx0-3412 ∷ CCZ123 ∷ [])
  (rw 1 (q40 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw 4 (q55 c4) ∷
   rw 8 (q56 c4) ∷
   rw 7 (q57 c4) ∷
   rw 6 (q58 c4) ∷
   rw 5 (q57 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 3 (q60 c4) ∷
   rw 2 (q52 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 0 (q40 c4) ∷
   rw⁻ 1 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = wpE 153 c4
  q65 : Ws → Eqn
  q65 c4 = wlE 308 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CZ23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = sE 49 (lem-cQ-at122331 c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 309 (lit c4)

-- box-tQ @122331: 13 steps
lem-box-tQ-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at122331 c4 = derive (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q64 c4) ∷
   re 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q64 c4) ∷
   rw 0 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

-- tP @122331: 7 steps
lem-tP-at122331 : Ws → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at122331 c4 = derive (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = sE 28 (lem-box-tQ-at13243241 c4)
  q70 : Ws → Eqn
  q70 c4 = wpE 163 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 164 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 165 c4
  q73 : Ws → Eqn
  q73 c4 = wlE 310 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = wlE 311 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = wpE 166 c4
  q76 : Ws → Eqn
  q76 c4 = wpE 11 c4
  q77 : Ws → Eqn
  q77 c4 = wpE 167 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 168 c4
  q79 : Ws → Eqn
  q79 c4 = wlE 312 (lit c4)

-- CXbc-box @13243241: 17 steps
lem-CXbc-box-at13243241 : Ws → ⟪ (CX42 ∷ Bx0-3421 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at13243241 c4 = derive (CX42 ∷ Bx0-3421 ∷ CX42 ∷ []) (Bx0-3421 ∷ CCZ134 ∷ [])
  (rw 1 (q69 c4) ∷
   rw 0 (q70 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 3 (q72 c4) ∷
   rw 2 (q70 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw⁻ 5 (q76 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   rw⁻ 4 (q77 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 1 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = wpE 169 c4
  q81 : Ws → Eqn
  q81 c4 = wlE 313 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wpE 170 c4
  q83 : Ws → Eqn
  q83 c4 = wlE 314 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = wpE 171 c4
  q85 : Ws → Eqn
  q85 c4 = wpE 172 c4
  q86 : Ws → Eqn
  q86 c4 = wpE 173 c4
  q87 : Ws → Eqn
  q87 c4 = wpE 174 c4
  q88 : Ws → Eqn
  q88 c4 = wlE 315 (lit c4)

-- CXcb-box @13243241: 18 steps
lem-CXcb-box-at13243241 : Ws → ⟪ (CX24 ∷ Bx0-3421 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at13243241 c4 = derive (CX24 ∷ Bx0-3421 ∷ CX24 ∷ []) (Bx0-3421 ∷ CCZ123 ∷ [])
  (rw 1 (q69 c4) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 2 (q81 c4) ∷
   rw⁻ 1 (q82 c4) ∷
   rw 4 (q83 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q85 c4) ∷
   rw 6 (q58 c4) ∷
   rw 5 (q85 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   rw 3 (q86 c4) ∷
   rw 2 (q80 c4) ∷
   rw 3 (q87 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 1 (q88 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = wpE 131 c4
  q90 : Ws → Eqn
  q90 c4 = sE 53 (lem-cQ-at132132 c4)

-- box-tQ @132132: 13 steps
lem-box-tQ-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at132132 c4 = derive (Bx0-3124 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q89 c4) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q89 c4) ∷
   rw 0 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q37 c4) ∷ []) Eq.refl

-- tP @132132: 7 steps
lem-tP-at132132 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at132132 c4 = derive (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q90 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = sE 29 (lem-box-tQ-at14233142 c4)
  q92 : Ws → Eqn
  q92 c4 = wlE 329 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = wpE 199 c4
  q94 : Ws → Eqn
  q94 c4 = wlE 330 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ012 ∷ CX43 ∷ []) (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀))
  q96 : Ws → Eqn
  q96 c4 = wlE 331 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = wlE 332 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = wlE 333 (lit c4)
  q99 : Ws → Eqn
  q99 c4 = wlE 277 (lit c4)

-- CXbc-box @14233142: 17 steps
lem-CXbc-box-at14233142 : Ws → ⟪ (CX31 ∷ Bx0-4312 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at14233142 c4 = derive (CX31 ∷ Bx0-4312 ∷ CX31 ∷ []) (Bx0-4312 ∷ CCZ234 ∷ [])
  (rw 1 (q91 c4) ∷
   rw 0 (q57 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw 3 (q93 c4) ∷
   rw 2 (q57 c4) ∷
   rw 5 (q94 c4) ∷
   rw⁻ 9 (q48 c4) ∷
   rw⁻ 8 (q95 c4) ∷
   rw⁻ 7 (q96 c4) ∷
   rw⁻ 6 (q95 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 6 (q94 c4) ∷
   rw⁻ 4 (q97 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw 4 (q98 c4) ∷
   rw⁻ 0 (q91 c4) ∷
   rw⁻ 1 (q99 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = wpE 200 c4
  q101 : Ws → Eqn
  q101 c4 = wpE 201 c4
  q102 : Ws → Eqn
  q102 c4 = wlE 167 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = wlE 334 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wpE 202 c4
  q105 : Ws → Eqn
  q105 c4 = wpE 203 c4
  q106 : Ws → Eqn
  q106 c4 = wpE 204 c4
  q107 : Ws → Eqn
  q107 c4 = wpE 205 c4
  q108 : Ws → Eqn
  q108 c4 = wlE 272 (lit c4)

-- CXcb-box @14233142: 18 steps
lem-CXcb-box-at14233142 : Ws → ⟪ (CX13 ∷ Bx0-4312 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at14233142 c4 = derive (CX13 ∷ Bx0-4312 ∷ CX13 ∷ []) (Bx0-4312 ∷ CCZ124 ∷ [])
  (rw 1 (q91 c4) ∷
   rw 0 (q100 c4) ∷
   rw⁻ 2 (q101 c4) ∷
   rw⁻ 1 (q102 c4) ∷
   rw 4 (q103 c4) ∷
   rw 8 (q104 c4) ∷
   rw 7 (q41 c4) ∷
   rw 6 (q58 c4) ∷
   rw 5 (q41 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw 3 (q105 c4) ∷
   rw 2 (q100 c4) ∷
   rw 3 (q106 c4) ∷
   rw⁻ 4 (q107 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw⁻ 0 (q91 c4) ∷
   rw⁻ 1 (q108 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = sE 74 (lem-tP-at14233142 c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 338 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wlE 339 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CZ12 ∷ Toff034 ∷ []) (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = wlE 340 (lit c4)

-- P-box @14233142: 8 steps
lem-P-box-at14233142 : Ws → ⟪ (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-P-box-at14233142 c4 = derive (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) (Bx0-4312 ∷ [])
  (rw 1 (q91 c4) ∷
   rw⁻ 0 (q109 c4) ∷
   rw⁻ 1 (q110 c4) ∷
   rw⁻ 3 (q109 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 2 (q112 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 0 (q91 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = wpE 5 c4
  q115 : Ws → Eqn
  q115 c4 = wlE 158 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (S0⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS))
  q117 : Ws → Eqn
  q117 c4 = eqn (Toff034 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (S0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS))
  q119 : Ws → Eqn
  q119 c4 = eqn (CS12⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))
  q120 : Ws → Eqn
  q120 c4 = wlE 159 (lit c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (S0 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑))
  q122 : Ws → Eqn
  q122 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))
  q123 : Ws → Eqn
  q123 c4 = eqn (S0⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))

-- VPQ @14233142: 14 steps
lem-VPQ-at14233142 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at14233142 c4 = derive (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 4 (q120 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw 0 (q115 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = wpE 210 c4
  q125 : Ws → Eqn
  q125 c4 = sE 64 (lem-cQ-at3443 c4)

-- box-tQ @3443: 13 steps
lem-box-tQ-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at3443 c4 = derive (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q124 c4) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q124 c4) ∷
   rw 0 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = wpE 211 c4
  q127 : Ws → Eqn
  q127 c4 = sE 54 (lem-cQ-at13213442 c4)

-- box-tQ @13213442: 13 steps
lem-box-tQ-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at13213442 c4 = derive (Bx0-3142 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q126 c4) ∷
   re 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q126 c4) ∷
   rw 0 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q127 c4) ∷
   rw 2 (q37 c4) ∷ []) Eq.refl

-- tP @13213442: 7 steps
lem-tP-at13213442 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at13213442 c4 = derive (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q127 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = wpE 214 c4
  q129 : Ws → Eqn
  q129 c4 = sE 59 (lem-cQ-at1441 c4)

-- box-tQ @1441: 13 steps
lem-box-tQ-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at1441 c4 = derive (Bx0-4231 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q128 c4) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q128 c4) ∷
   rw 0 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = wpE 154 c4
  q131 : Ws → Eqn
  q131 c4 = sE 55 (lem-cQ-at1331 c4)

-- box-tQ @1331: 13 steps
lem-box-tQ-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at1331 c4 = derive (Bx0-3214 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q130 c4) ∷
   re 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q130 c4) ∷
   rw 0 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

-- tP @1331: 7 steps
lem-tP-at1331 : Ws → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at1331 c4 = derive (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q131 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = wlE 344 (lit c4)
  q133 : Ws → Eqn
  q133 c4 = sE 63 (lem-cQ-at2442 c4)

-- box-tQ @2442: 13 steps
lem-box-tQ-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at2442 c4 = derive (Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q132 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q132 c4) ∷
   rw 0 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q23 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = wpE 218 c4
  q135 : Ws → Eqn
  q135 c4 = sE 50 (lem-cQ-at12233441 c4)

-- box-tQ @12233441: 13 steps
lem-box-tQ-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at12233441 c4 = derive (Bx0-2341 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q134 c4) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q134 c4) ∷
   rw 0 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 1 (q135 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = wlE 394 (lit c4)
  q137 : Ws → Eqn
  q137 c4 = wlE 395 (lit c4)
  q138 : Ws → Eqn
  q138 c4 = wlE 396 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = sE 32 (lem-cQ-at0110 c4)

-- tP @0110: 7 steps
lem-tP-at0110 : Ws → ⟪ (Toff102 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff102 ∷ []) ⟫ʷ
lem-tP-at0110 c4 = derive (Toff102 ∷ Toff134 ∷ []) (Toff134 ∷ Toff102 ∷ [])
  (rw⁻ 0 (q136 c4) ∷
   rw⁻ 3 (q137 c4) ∷
   rw 2 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw⁻ 2 (q138 c4) ∷
   rw 0 (q137 c4) ∷
   rw 1 (q136 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = wpE 217 c4
  q141 : Ws → Eqn
  q141 c4 = sE 56 (lem-cQ-at133441 c4)

-- box-tQ @133441: 13 steps
lem-box-tQ-at133441 : Ws → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at133441 c4 = derive (Bx0-3241 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q140 c4) ∷
   re 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q140 c4) ∷
   rw 0 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 1 (q141 c4) ∷
   rw 2 (q68 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = sE 73 (lem-tP-at13243241 c4)

-- P-box @13243241: 8 steps
lem-P-box-at13243241 : Ws → ⟪ (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-P-box-at13243241 c4 = derive (Toff012 ∷ Bx0-3421 ∷ Toff012 ∷ []) (Bx0-3421 ∷ [])
  (rw 1 (q69 c4) ∷
   rw⁻ 0 (q142 c4) ∷
   rw⁻ 1 (q110 c4) ∷
   rw⁻ 3 (q142 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 2 (q112 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 0 (q69 c4) ∷ []) Eq.refl

-- VPQ @13243241: 14 steps
lem-VPQ-at13243241 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at13243241 c4 = derive (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 4 (q120 c4) ∷
   rw 3 (q142 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw 0 (q115 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = wpE 212 c4
  q144 : Ws → Eqn
  q144 c4 = sE 61 (lem-cQ-at233442 c4)

-- box-tQ @233442: 13 steps
lem-box-tQ-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at233442 c4 = derive (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q143 c4) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q143 c4) ∷
   rw 0 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q144 c4) ∷
   rw 2 (q37 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = wlE 418 (lit c4)
  q146 : Ws → Eqn
  q146 c4 = wlE 419 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (S2⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS))
  q148 : Ws → Eqn
  q148 c4 = eqn (Toff201 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS))
  q149 : Ws → Eqn
  q149 c4 = eqn (S2 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS))
  q150 : Ws → Eqn
  q150 c4 = eqn (CS01⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑))
  q151 : Ws → Eqn
  q151 c4 = wlE 179 (lit c4)
  q152 : Ws → Eqn
  q152 c4 = sE 65 (lem-tP-at021021 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (CS01⁻ ∷ S2 ∷ []) (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S))
  q154 : Ws → Eqn
  q154 c4 = eqn (CS01⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff))
  q155 : Ws → Eqn
  q155 c4 = eqn (CS01⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S))

-- VPQ @021021: 14 steps
lem-VPQ-at021021 : Ws → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at021021 c4 = derive (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q145 c4) ∷
   rw⁻ 4 (q146 c4) ∷
   rw 3 (q147 c4) ∷
   rw 2 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 0 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw 3 (q152 c4) ∷
   rw⁻ 4 (q151 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q155 c4) ∷
   rw 0 (q146 c4) ∷
   rw 2 (q145 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = sE 72 (lem-tP-at13243142 c4)

-- P-box @13243142: 8 steps
lem-P-box-at13243142 : Ws → ⟪ (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-P-box-at13243142 c4 = derive (Toff012 ∷ Bx0-3412 ∷ Toff012 ∷ []) (Bx0-3412 ∷ [])
  (rw 1 (q40 c4) ∷
   rw⁻ 0 (q156 c4) ∷
   rw⁻ 1 (q110 c4) ∷
   rw⁻ 3 (q156 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 2 (q112 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 0 (q40 c4) ∷ []) Eq.refl

-- VPQ @13243142: 14 steps
lem-VPQ-at13243142 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at13243142 c4 = derive (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 4 (q120 c4) ∷
   rw 3 (q156 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw 0 (q115 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = wlE 437 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = wlE 438 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wlE 439 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (Toff301 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff301 ∷ []) (lem-comm-TOFF301-CSd24 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = wlE 440 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CS01⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q163 : Ws → Eqn
  q163 c4 = wlE 441 (lit c4)
  q164 : Ws → Eqn
  q164 c4 = sE 68 (lem-tP-at03102132 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CS01⁻ ∷ S3 ∷ []) (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑))
  q166 : Ws → Eqn
  q166 c4 = eqn (CS01⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))
  q167 : Ws → Eqn
  q167 c4 = eqn (CS01⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑))

-- VPQ @03102132: 14 steps
lem-VPQ-at03102132 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at03102132 c4 = derive (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q157 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   rw⁻ 3 (q159 c4) ∷
   rw 2 (q160 c4) ∷
   rw⁻ 1 (q161 c4) ∷
   rw 0 (q162 c4) ∷
   rw 4 (q163 c4) ∷
   rw 3 (q164 c4) ∷
   rw⁻ 4 (q163 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   rw 3 (q167 c4) ∷
   rw 0 (q158 c4) ∷
   rw 2 (q157 c4) ∷ []) Eq.refl

-- tP @3443: 7 steps
lem-tP-at3443 : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at3443 c4 = derive (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q125 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = wpE 304 c4
  q169 : Ws → Eqn
  q169 c4 = wlE 455 (lit c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (CS23⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S))
  q171 : Ws → Eqn
  q171 c4 = eqn (Toff401 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff401 ∷ []) (lem-comm-TOFF401-CSd23 (lit c4))
  q172 : Ws → Eqn
  q172 c4 = eqn (CS23⁻ ∷ S4 ∷ []) (S4 ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S))
  q173 : Ws → Eqn
  q173 c4 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS))
  q174 : Ws → Eqn
  q174 c4 = wlE 456 (lit c4)
  q175 : Ws → Eqn
  q175 c4 = sE 70 (lem-tP-at0410213243 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (CS01⁻ ∷ S4 ∷ []) (S4 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑ ↑))
  q177 : Ws → Eqn
  q177 c4 = eqn (CS01⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ))
  q178 : Ws → Eqn
  q178 c4 = eqn (CS01⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑))

-- VPQ @0410213243: 14 steps
lem-VPQ-at0410213243 : Ws → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at0410213243 c4 = derive (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q168 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw⁻ 3 (q170 c4) ∷
   rw 2 (q171 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 0 (q173 c4) ∷
   rw 4 (q174 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q174 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q178 c4) ∷
   rw 0 (q169 c4) ∷
   rw 2 (q168 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = wlE 465 (lit c4)
  q180 : Ws → Eqn
  q180 c4 = sE 46 (lem-cQ-at043043 c4)
  q181 : Ws → Eqn
  q181 c4 = wlE 466 (lit c4)

-- box-tQ @043043: 13 steps
lem-box-tQ-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at043043 c4 = derive (Bx4-1203 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q124 c4) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q124 c4) ∷
   rw 0 (q179 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q180 c4) ∷
   rw 2 (q181 c4) ∷ []) Eq.refl

private
  q182 : Ws → Eqn
  q182 c4 = wlE 467 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = wpE 315 c4
  q184 : Ws → Eqn
  q184 c4 = wlE 454 (lit c4)

-- tP @043043: 7 steps
lem-tP-at043043 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at043043 c4 = derive (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  (rw⁻ 0 (q182 c4) ∷
   rw⁻ 3 (q183 c4) ∷
   rw 2 (q184 c4) ∷
   rw 1 (q180 c4) ∷
   rw⁻ 2 (q184 c4) ∷
   rw 0 (q183 c4) ∷
   rw 1 (q182 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = wlE 473 (lit c4)
  q186 : Ws → Eqn
  q186 c4 = sE 44 (lem-cQ-at0330 c4)
  q187 : Ws → Eqn
  q187 c4 = wlE 474 (lit c4)

-- box-tQ @0330: 13 steps
lem-box-tQ-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0330 c4 = derive (Bx3-1204 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q5 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q5 c4) ∷
   rw 0 (q185 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q186 c4) ∷
   rw 2 (q187 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = sE 71 (lem-tP-at04203243 c4)

-- VPQ @04203243: 14 steps
lem-VPQ-at04203243 : Ws → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at04203243 c4 = derive (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q168 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw⁻ 3 (q170 c4) ∷
   rw 2 (q171 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 0 (q173 c4) ∷
   rw 4 (q174 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 4 (q174 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q178 c4) ∷
   rw 0 (q169 c4) ∷
   rw 2 (q168 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = wlE 487 (lit c4)
  q190 : Ws → Eqn
  q190 c4 = wpE 343 c4
  q191 : Ws → Eqn
  q191 c4 = wlE 436 (lit c4)

-- tP @0330: 7 steps
lem-tP-at0330 : Ws → ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-tP-at0330 c4 = derive (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q189 c4) ∷
   rw⁻ 3 (q190 c4) ∷
   rw 2 (q191 c4) ∷
   rw 1 (q186 c4) ∷
   rw⁻ 2 (q191 c4) ∷
   rw 0 (q190 c4) ∷
   rw 1 (q189 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = wlE 493 (lit c4)
  q193 : Ws → Eqn
  q193 c4 = wpE 353 c4
  q194 : Ws → Eqn
  q194 c4 = sE 39 (lem-cQ-at0310243142 c4)
  q195 : Ws → Eqn
  q195 c4 = wpE 354 c4

-- box-tQ @0310243142: 13 steps
lem-box-tQ-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q192 c4) ∷
   re 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q192 c4) ∷
   rw 0 (q193 c4) ∷
   rw 2 (q15 c4) ∷
   rw 1 (q194 c4) ∷
   rw 2 (q195 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = sE 42 (lem-cQ-at0314203142 c4)

-- tP @0314203142: 7 steps
lem-tP-at0314203142 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0314203142 c4 = derive (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q190 c4) ∷
   rw⁻ 3 (q189 c4) ∷
   rw 2 (q191 c4) ∷
   rw 1 (q196 c4) ∷
   rw⁻ 2 (q191 c4) ∷
   rw 0 (q189 c4) ∷
   rw 1 (q190 c4) ∷ []) Eq.refl

-- tP @0310243142: 7 steps
lem-tP-at0310243142 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0310243142 c4 = derive (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q190 c4) ∷
   rw⁻ 3 (q189 c4) ∷
   rw 2 (q191 c4) ∷
   rw 1 (q194 c4) ∷
   rw⁻ 2 (q191 c4) ∷
   rw 0 (q189 c4) ∷
   rw 1 (q190 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = sE 26 (lem-box-tQ-at04203243 c4)
  q198 : Ws → Eqn
  q198 c4 = wpE 360 c4
  q199 : Ws → Eqn
  q199 c4 = wpE 361 c4
  q200 : Ws → Eqn
  q200 c4 = wpE 362 c4
  q201 : Ws → Eqn
  q201 c4 = wlE 477 (lit c4)
  q202 : Ws → Eqn
  q202 c4 = wlE 433 (lit c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q204 : Ws → Eqn
  q204 c4 = wpE 363 c4
  q205 : Ws → Eqn
  q205 c4 = wpE 294 c4
  q206 : Ws → Eqn
  q206 c4 = wpE 129 c4
  q207 : Ws → Eqn
  q207 c4 = wpE 364 c4
  q208 : Ws → Eqn
  q208 c4 = wlE 479 (lit c4)

-- CXbc-box @04203243: 17 steps
lem-CXbc-box-at04203243 : Ws → ⟪ (CX02 ∷ Bx4-1023 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at04203243 c4 = derive (CX02 ∷ Bx4-1023 ∷ CX02 ∷ []) (Bx4-1023 ∷ CCZ013 ∷ [])
  (rw 1 (q197 c4) ∷
   rw 0 (q198 c4) ∷
   rw⁻ 1 (q199 c4) ∷
   rw 3 (q200 c4) ∷
   rw 2 (q198 c4) ∷
   rw 5 (q201 c4) ∷
   rw⁻ 9 (q202 c4) ∷
   rw 8 (q203 c4) ∷
   rw⁻ 7 (q204 c4) ∷
   rw 6 (q203 c4) ∷
   rw⁻ 5 (q205 c4) ∷
   rw⁻ 6 (q201 c4) ∷
   rw 4 (q206 c4) ∷
   rw⁻ 3 (q199 c4) ∷
   rw 4 (q207 c4) ∷
   rw⁻ 0 (q197 c4) ∷
   rw⁻ 1 (q208 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = wpE 365 c4
  q210 : Ws → Eqn
  q210 c4 = wlE 507 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = wpE 366 c4
  q212 : Ws → Eqn
  q212 c4 = wlE 207 (lit c4)
  q213 : Ws → Eqn
  q213 c4 = wpE 367 c4
  q214 : Ws → Eqn
  q214 c4 = wpE 368 c4
  q215 : Ws → Eqn
  q215 c4 = eqn (CS23⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 (lit c4))
  q216 : Ws → Eqn
  q216 c4 = eqn (CS23 ∷ Toff401 ∷ []) (Toff401 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF401 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = wpE 335 c4
  q218 : Ws → Eqn
  q218 c4 = wpE 369 c4
  q219 : Ws → Eqn
  q219 c4 = wlE 508 (lit c4)
  q220 : Ws → Eqn
  q220 c4 = wlE 476 (lit c4)

-- CXcb-box @04203243: 18 steps
lem-CXcb-box-at04203243 : Ws → ⟪ (CX20 ∷ Bx4-1023 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at04203243 c4 = derive (CX20 ∷ Bx4-1023 ∷ CX20 ∷ []) (Bx4-1023 ∷ CCZ123 ∷ [])
  (rw 1 (q197 c4) ∷
   rw 0 (q209 c4) ∷
   rw⁻ 2 (q210 c4) ∷
   rw⁻ 1 (q211 c4) ∷
   rw 4 (q212 c4) ∷
   rw 8 (q213 c4) ∷
   rw 7 (q214 c4) ∷
   rw 6 (q215 c4) ∷
   rw 5 (q214 c4) ∷
   rw 4 (q216 c4) ∷
   rw⁻ 5 (q212 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw 2 (q209 c4) ∷
   rw 3 (q218 c4) ∷
   rw 4 (q219 c4) ∷
   rw⁻ 3 (q211 c4) ∷
   rw⁻ 0 (q197 c4) ∷
   rw⁻ 1 (q220 c4) ∷ []) Eq.refl

private
  q221 : Ws → Eqn
  q221 c4 = sE 25 (lem-box-tQ-at032032 c4)
  q222 : Ws → Eqn
  q222 c4 = wlE 521 (lit c4)
  q223 : Ws → Eqn
  q223 c4 = wpE 377 c4
  q224 : Ws → Eqn
  q224 c4 = wpE 341 c4
  q225 : Ws → Eqn
  q225 c4 = wlE 452 (lit c4)
  q226 : Ws → Eqn
  q226 c4 = wpE 342 c4
  q227 : Ws → Eqn
  q227 c4 = wpE 302 c4
  q228 : Ws → Eqn
  q228 c4 = wpE 378 c4

-- CXbc-box @032032: 17 steps
lem-CXbc-box-at032032 : Ws → ⟪ (CX02 ∷ Bx3-1024 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at032032 c4 = derive (CX02 ∷ Bx3-1024 ∷ CX02 ∷ []) (Bx3-1024 ∷ CCZ014 ∷ [])
  (rw 1 (q221 c4) ∷
   rw 0 (q222 c4) ∷
   rw⁻ 1 (q199 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q222 c4) ∷
   rw 5 (q224 c4) ∷
   rw⁻ 9 (q225 c4) ∷
   rw 8 (q203 c4) ∷
   rw⁻ 7 (q226 c4) ∷
   rw 6 (q203 c4) ∷
   rw⁻ 5 (q227 c4) ∷
   rw⁻ 6 (q224 c4) ∷
   rw 4 (q206 c4) ∷
   rw⁻ 3 (q199 c4) ∷
   rw 4 (q207 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw⁻ 1 (q228 c4) ∷ []) Eq.refl

private
  q229 : Ws → Eqn
  q229 c4 = wlE 522 (lit c4)
  q230 : Ws → Eqn
  q230 c4 = wlE 523 (lit c4)
  q231 : Ws → Eqn
  q231 c4 = wlE 256 (lit c4)
  q232 : Ws → Eqn
  q232 c4 = wpE 379 c4
  q233 : Ws → Eqn
  q233 c4 = wlE 524 (lit c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (CS24⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4))
  q235 : Ws → Eqn
  q235 c4 = eqn (CS24 ∷ Toff301 ∷ []) (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4))
  q236 : Ws → Eqn
  q236 c4 = wlE 525 (lit c4)
  q237 : Ws → Eqn
  q237 c4 = wlE 526 (lit c4)
  q238 : Ws → Eqn
  q238 c4 = wlE 527 (lit c4)
  q239 : Ws → Eqn
  q239 c4 = wpE 380 c4

-- CXcb-box @032032: 18 steps
lem-CXcb-box-at032032 : Ws → ⟪ (CX20 ∷ Bx3-1024 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at032032 c4 = derive (CX20 ∷ Bx3-1024 ∷ CX20 ∷ []) (Bx3-1024 ∷ CCZ124 ∷ [])
  (rw 1 (q221 c4) ∷
   rw 0 (q229 c4) ∷
   rw⁻ 2 (q230 c4) ∷
   rw⁻ 1 (q211 c4) ∷
   rw 4 (q231 c4) ∷
   rw 8 (q232 c4) ∷
   rw 7 (q233 c4) ∷
   rw 6 (q234 c4) ∷
   rw 5 (q233 c4) ∷
   rw 4 (q235 c4) ∷
   rw⁻ 5 (q231 c4) ∷
   rw⁻ 3 (q236 c4) ∷
   rw 2 (q229 c4) ∷
   rw 3 (q237 c4) ∷
   rw 4 (q238 c4) ∷
   rw⁻ 3 (q211 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw⁻ 1 (q239 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = wlE 610 (lit c4)
  q241 : Ws → Eqn
  q241 c4 = sE 36 (lem-cQ-at0214203143 c4)

-- box-tQ @0214203143: 13 steps
lem-box-tQ-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q240 c4) ∷
   re 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q240 c4) ∷
   rw 0 (q14 c4) ∷
   rw 2 (q15 c4) ∷
   rw 1 (q241 c4) ∷
   rw 2 (q16 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = wpE 216 c4
  q243 : Ws → Eqn
  q243 c4 = wlE 622 (lit c4)
  q244 : Ws → Eqn
  q244 c4 = sE 37 (lem-cQ-at0214213043 c4)
  q245 : Ws → Eqn
  q245 c4 = wlE 623 (lit c4)

-- box-tQ @0214213043: 13 steps
lem-box-tQ-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q242 c4) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q242 c4) ∷
   rw 0 (q243 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q245 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = wlE 624 (lit c4)
  q247 : Ws → Eqn
  q247 c4 = wlE 625 (lit c4)

-- tP @0214213043: 7 steps
lem-tP-at0214213043 : Ws → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at0214213043 c4 = derive (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  (rw⁻ 0 (q246 c4) ∷
   rw⁻ 3 (q247 c4) ∷
   rw 2 (q11 c4) ∷
   rw 1 (q244 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 0 (q247 c4) ∷
   rw 1 (q246 c4) ∷ []) Eq.refl

private
  q248 : Ws → Eqn
  q248 c4 = wpE 516 c4
  q249 : Ws → Eqn
  q249 c4 = wlE 640 (lit c4)
  q250 : Ws → Eqn
  q250 c4 = eqn (CZ03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4))
  q251 : Ws → Eqn
  q251 c4 = sE 33 (lem-cQ-at0210233441 c4)
  q252 : Ws → Eqn
  q252 c4 = wlE 641 (lit c4)

-- box-tQ @0210233441: 13 steps
lem-box-tQ-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q248 c4) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q248 c4) ∷
   rw 0 (q249 c4) ∷
   rw 2 (q250 c4) ∷
   rw 1 (q251 c4) ∷
   rw 2 (q252 c4) ∷ []) Eq.refl

-- tP @0210233441: 7 steps
lem-tP-at0210233441 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at0210233441 c4 = derive (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  (rw⁻ 0 (q247 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw 2 (q11 c4) ∷
   rw 1 (q251 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 0 (q246 c4) ∷
   rw 1 (q247 c4) ∷ []) Eq.refl

-- tP @12233441: 7 steps
lem-tP-at12233441 : Ws → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at12233441 c4 = derive (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q135 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷ []) Eq.refl

private
  q253 : Ws → Eqn
  q253 c4 = sE 57 (lem-cQ-at14213243 c4)

-- box-tQ @14213243: 13 steps
lem-box-tQ-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at14213243 c4 = derive (Bx0-4123 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q242 c4) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q242 c4) ∷
   rw 0 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q253 c4) ∷
   rw 2 (q23 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = wpE 180 c4
  q255 : Ws → Eqn
  q255 c4 = sE 58 (lem-cQ-at143143 c4)

-- box-tQ @143143: 13 steps
lem-box-tQ-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at143143 c4 = derive (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q254 c4) ∷
   re 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q254 c4) ∷
   rw 0 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q255 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

-- tP @143143: 7 steps
lem-tP-at143143 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at143143 c4 = derive (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q24 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q255 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q24 c4) ∷ []) Eq.refl

-- tP @233442: 7 steps
lem-tP-at233442 : Ws → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at233442 c4 = derive (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q144 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = sE 66 (lem-tP-at0210213443 c4)

-- VPQ @0210213443: 14 steps
lem-VPQ-at0210213443 : Ws → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0210213443 c4 = derive (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q145 c4) ∷
   rw⁻ 4 (q146 c4) ∷
   rw 3 (q147 c4) ∷
   rw 2 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 0 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw 3 (q256 c4) ∷
   rw⁻ 4 (q151 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q155 c4) ∷
   rw 0 (q146 c4) ∷
   rw 2 (q145 c4) ∷ []) Eq.refl

private
  q257 : Ws → Eqn
  q257 c4 = sE 30 (lem-box-tQ-at14233241 c4)
  q258 : Ws → Eqn
  q258 c4 = sE 75 (lem-tP-at14233241 c4)

-- P-box @14233241: 8 steps
lem-P-box-at14233241 : Ws → ⟪ (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-P-box-at14233241 c4 = derive (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) (Bx0-4321 ∷ [])
  (rw 1 (q257 c4) ∷
   rw⁻ 0 (q258 c4) ∷
   rw⁻ 1 (q110 c4) ∷
   rw⁻ 3 (q258 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 2 (q112 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 0 (q257 c4) ∷ []) Eq.refl

-- VPQ @14233241: 14 steps
lem-VPQ-at14233241 : Ws → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at14233241 c4 = derive (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q114 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 4 (q120 c4) ∷
   rw 3 (q258 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw 0 (q115 c4) ∷
   rw 2 (q114 c4) ∷ []) Eq.refl

private
  q259 : Ws → Eqn
  q259 c4 = wpE 598 c4
  q260 : Ws → Eqn
  q260 c4 = sE 48 (lem-cQ-at12213443 c4)

-- box-tQ @12213443: 13 steps
lem-box-tQ-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at12213443 c4 = derive (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw 2 (q259 c4) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw 5 (q259 c4) ∷
   rw 0 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q260 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

-- tP @12213443: 7 steps
lem-tP-at12213443 : Ws → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at12213443 c4 = derive (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q260 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = wpE 661 c4
  q262 : Ws → Eqn
  q262 c4 = wlE 749 (lit c4)
  q263 : Ws → Eqn
  q263 c4 = sE 43 (lem-cQ-at0314213042 c4)
  q264 : Ws → Eqn
  q264 c4 = wlE 750 (lit c4)

-- box-tQ @0314213042: 13 steps
lem-box-tQ-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q261 c4) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q261 c4) ∷
   rw 0 (q262 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q263 c4) ∷
   rw 2 (q264 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = sE 35 (lem-cQ-at0213203441 c4)

-- tP @0213203441: 7 steps
lem-tP-at0213203441 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at0213203441 c4 = derive (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  (rw⁻ 0 (q247 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw 2 (q11 c4) ∷
   rw 1 (q265 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 0 (q246 c4) ∷
   rw 1 (q247 c4) ∷ []) Eq.refl

private
  q266 : Ws → Eqn
  q266 c4 = wlE 494 (lit c4)

-- box-tQ @0314203142: 13 steps
lem-box-tQ-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q266 c4) ∷
   re 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q266 c4) ∷
   rw 0 (q193 c4) ∷
   rw 2 (q15 c4) ∷
   rw 1 (q196 c4) ∷
   rw 2 (q195 c4) ∷ []) Eq.refl

private
  q267 : Ws → Eqn
  q267 c4 = wlE 781 (lit c4)
  q268 : Ws → Eqn
  q268 c4 = wlE 782 (lit c4)

-- tP @0314213042: 7 steps
lem-tP-at0314213042 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at0314213042 c4 = derive (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q267 c4) ∷
   rw⁻ 3 (q268 c4) ∷
   rw 2 (q191 c4) ∷
   rw 1 (q263 c4) ∷
   rw⁻ 2 (q191 c4) ∷
   rw 0 (q268 c4) ∷
   rw 1 (q267 c4) ∷ []) Eq.refl

private
  q269 : Ws → Eqn
  q269 c4 = sE 69 (lem-tP-at032032 c4)
  q270 : Ws → Eqn
  q270 c4 = wlE 842 (lit c4)
  q271 : Ws → Eqn
  q271 c4 = wlE 843 (lit c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (CZ24 ∷ Toff301 ∷ []) (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4))
  q273 : Ws → Eqn
  q273 c4 = wlE 844 (lit c4)

-- P-box @032032: 8 steps
lem-P-box-at032032 : Ws → ⟪ (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-P-box-at032032 c4 = derive (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) (Bx3-1024 ∷ [])
  (rw 1 (q221 c4) ∷
   rw⁻ 0 (q269 c4) ∷
   rw⁻ 1 (q270 c4) ∷
   rw⁻ 3 (q269 c4) ∷
   rw⁻ 4 (q271 c4) ∷
   rw 2 (q272 c4) ∷
   rw⁻ 3 (q273 c4) ∷
   rw⁻ 0 (q221 c4) ∷ []) Eq.refl

-- VPQ @032032: 14 steps
lem-VPQ-at032032 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at032032 c4 = derive (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q157 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   rw⁻ 3 (q159 c4) ∷
   rw 2 (q160 c4) ∷
   rw⁻ 1 (q161 c4) ∷
   rw 0 (q162 c4) ∷
   rw 4 (q163 c4) ∷
   rw 3 (q269 c4) ∷
   rw⁻ 4 (q163 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   rw 3 (q167 c4) ∷
   rw 0 (q158 c4) ∷
   rw 2 (q157 c4) ∷ []) Eq.refl

private
  q274 : Ws → Eqn
  q274 c4 = wlE 845 (lit c4)
  q275 : Ws → Eqn
  q275 c4 = wlE 846 (lit c4)
  q276 : Ws → Eqn
  q276 c4 = sE 41 (lem-cQ-at0312243140 c4)
  q277 : Ws → Eqn
  q277 c4 = wlE 847 (lit c4)

-- box-tQ @0312243140: 13 steps
lem-box-tQ-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at0312243140 c4 = derive (Bx3-2410 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q274 c4) ∷
   re 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q274 c4) ∷
   rw 0 (q275 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q276 c4) ∷
   rw 2 (q277 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = wpE 733 c4
  q279 : Ws → Eqn
  q279 c4 = sE 45 (lem-cQ-at033440 c4)

-- box-tQ @033440: 13 steps
lem-box-tQ-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at033440 c4 = derive (Bx3-1240 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q278 c4) ∷
   re 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q278 c4) ∷
   rw 0 (q185 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q279 c4) ∷
   rw 2 (q187 c4) ∷ []) Eq.refl

private
  q280 : Ws → Eqn
  q280 c4 = wpE 732 c4
  q281 : Ws → Eqn
  q281 c4 = sE 40 (lem-cQ-at0312213440 c4)

-- box-tQ @0312213440: 13 steps
lem-box-tQ-at0312213440 : Ws → ⟪ (Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0312213440 c4 = derive (Bx3-2140 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q280 c4) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q280 c4) ∷
   rw 0 (q185 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q281 c4) ∷
   rw 2 (q187 c4) ∷ []) Eq.refl

private
  q282 : Ws → Eqn
  q282 c4 = wlE 435 (lit c4)
  q283 : Ws → Eqn
  q283 c4 = wlE 434 (lit c4)

-- tP @0312243140: 7 steps
lem-tP-at0312243140 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at0312243140 c4 = derive (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  (rw⁻ 0 (q282 c4) ∷
   rw⁻ 3 (q283 c4) ∷
   rw 2 (q191 c4) ∷
   rw 1 (q276 c4) ∷
   rw⁻ 2 (q191 c4) ∷
   rw 0 (q283 c4) ∷
   rw 1 (q282 c4) ∷ []) Eq.refl

private
  q284 : Ws → Eqn
  q284 c4 = wlE 915 (lit c4)
  q285 : Ws → Eqn
  q285 c4 = sE 38 (lem-cQ-at022330 c4)
  q286 : Ws → Eqn
  q286 c4 = wlE 916 (lit c4)

-- box-tQ @022330: 13 steps
lem-box-tQ-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at022330 c4 = derive (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q33 c4) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q33 c4) ∷
   rw 0 (q284 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q285 c4) ∷
   rw 2 (q286 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = wlE 924 (lit c4)
  q288 : Ws → Eqn
  q288 c4 = wlE 925 (lit c4)
  q289 : Ws → Eqn
  q289 c4 = wlE 926 (lit c4)
  q290 : Ws → Eqn
  q290 c4 = wlE 927 (lit c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (Sw03 ∷ Bx2-14 ∷ []) (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4))
  q292 : Ws → Eqn
  q292 c4 = wlE 928 (lit c4)

-- nat-SWbc @022330: 23 steps
lem-nat-SWbc-at022330 : Ws → ⟪ (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-nat-SWbc-at022330 c4 = derive (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (Bx2-1034 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) ∷
   rw⁻ 0 (q287 c4) ∷
   rw 1 (q288 c4) ∷
   re 3 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   rw⁻ 2 (q289 c4) ∷
   rw 3 (q290 c4) ∷
   rw 4 (q291 c4) ∷
   rw 5 (q290 c4) ∷
   rw⁻ 6 (q289 c4) ∷
   rw 7 (q291 c4) ∷
   rw 8 (q288 c4) ∷
   rw⁻ 9 (q287 c4) ∷
   re 11 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   rw⁻ 10 (q289 c4) ∷
   rw 11 (q290 c4) ∷
   rw 12 (q291 c4) ∷
   rw 13 (q290 c4) ∷
   rw⁻ 14 (q289 c4) ∷
   rw 15 (q291 c4) ∷
   rw 16 (q292 c4) ∷
   re 2 6 (Bx1-234 ∷ []) ∷
   re 5 6 (Bx1-234 ∷ []) ∷
   re 0 6 (Bx2-1034 ∷ []) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = sE 24 (lem-box-tQ-at0220 c4)
  q294 : Ws → Eqn
  q294 c4 = sE 67 (lem-tP-at0220 c4)
  q295 : Ws → Eqn
  q295 c4 = wlE 932 (lit c4)
  q296 : Ws → Eqn
  q296 c4 = wlE 933 (lit c4)
  q297 : Ws → Eqn
  q297 c4 = eqn (Toff201 ∷ CZ34 ∷ []) (CZ34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CZ))
  q298 : Ws → Eqn
  q298 c4 = wlE 934 (lit c4)

-- P-box @0220: 8 steps
lem-P-box-at0220 : Ws → ⟪ (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-P-box-at0220 c4 = derive (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) (Bx2-1034 ∷ [])
  (rw 1 (q293 c4) ∷
   rw⁻ 0 (q294 c4) ∷
   rw⁻ 1 (q295 c4) ∷
   rw⁻ 3 (q294 c4) ∷
   rw⁻ 4 (q296 c4) ∷
   rw⁻ 2 (q297 c4) ∷
   rw⁻ 3 (q298 c4) ∷
   rw⁻ 0 (q293 c4) ∷ []) Eq.refl

-- VPQ @0220: 14 steps
lem-VPQ-at0220 : Ws → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0220 c4 = derive (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  (rw⁻ 0 (q145 c4) ∷
   rw⁻ 4 (q146 c4) ∷
   rw 3 (q147 c4) ∷
   rw 2 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 0 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw 3 (q294 c4) ∷
   rw⁻ 4 (q151 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q155 c4) ∷
   rw 0 (q146 c4) ∷
   rw 2 (q145 c4) ∷ []) Eq.refl

private
  q299 : Ws → Eqn
  q299 c4 = sE 23 (lem-box-tQ-at0213243140 c4)
  q300 : Ws → Eqn
  q300 c4 = wlE 938 (lit c4)
  q301 : Ws → Eqn
  q301 c4 = wpE 290 c4
  q302 : Ws → Eqn
  q302 c4 = wpE 115 c4
  q303 : Ws → Eqn
  q303 c4 = wlE 268 (lit c4)
  q304 : Ws → Eqn
  q304 c4 = wpE 116 c4
  q305 : Ws → Eqn
  q305 c4 = wpE 117 c4
  q306 : Ws → Eqn
  q306 c4 = wpE 560 c4

-- CXbc-box @0213243140: 17 steps
lem-CXbc-box-at0213243140 : Ws → ⟪ (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0213243140 c4 = derive (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) (Bx2-3410 ∷ CCZ034 ∷ [])
  (rw 1 (q299 c4) ∷
   rw 0 (q300 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 3 (q301 c4) ∷
   rw 2 (q300 c4) ∷
   rw 5 (q302 c4) ∷
   rw⁻ 9 (q303 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw⁻ 7 (q304 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw⁻ 5 (q305 c4) ∷
   rw⁻ 6 (q302 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw 4 (q50 c4) ∷
   rw⁻ 0 (q299 c4) ∷
   rw⁻ 1 (q306 c4) ∷ []) Eq.refl

private
  q307 : Ws → Eqn
  q307 c4 = wlE 939 (lit c4)
  q308 : Ws → Eqn
  q308 c4 = wlE 940 (lit c4)
  q309 : Ws → Eqn
  q309 c4 = wlE 323 (lit c4)
  q310 : Ws → Eqn
  q310 c4 = wpE 292 c4
  q311 : Ws → Eqn
  q311 c4 = wlE 941 (lit c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (CS01 ∷ Toff234 ∷ []) (Toff234 ∷ CS01 ∷ []) (c₂ (CS) (Toff))
  q313 : Ws → Eqn
  q313 c4 = wlE 942 (lit c4)
  q314 : Ws → Eqn
  q314 c4 = wlE 943 (lit c4)
  q315 : Ws → Eqn
  q315 c4 = wlE 704 (lit c4)
  q316 : Ws → Eqn
  q316 c4 = wpE 565 c4

-- CXcb-box @0213243140: 18 steps
lem-CXcb-box-at0213243140 : Ws → ⟪ (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0213243140 c4 = derive (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) (Bx2-3410 ∷ CCZ013 ∷ [])
  (rw 1 (q299 c4) ∷
   rw 0 (q307 c4) ∷
   rw⁻ 2 (q308 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw 4 (q309 c4) ∷
   rw 8 (q310 c4) ∷
   rw 7 (q311 c4) ∷
   rw 6 (q154 c4) ∷
   rw 5 (q311 c4) ∷
   rw 4 (q312 c4) ∷
   rw⁻ 5 (q309 c4) ∷
   rw 3 (q313 c4) ∷
   rw 2 (q307 c4) ∷
   rw 3 (q314 c4) ∷
   rw⁻ 4 (q315 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 0 (q299 c4) ∷
   rw⁻ 1 (q316 c4) ∷ []) Eq.refl
