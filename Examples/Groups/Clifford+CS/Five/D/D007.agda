{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD007 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D007 (Sᴰ : SD007) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-TOFF034 ; lem-comm-CSd12-TOFF034 ; lem-comm-CZ04-CCZ123 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ24-CCZ013 ; lem-comm-TOFF301-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-TOFF401 ; lem-comm-CS24-TOFF301 ; lem-comm-CSd23-TOFF401 ; lem-comm-CSd24-TOFF301 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ24-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CZ02-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-SWAP03-BOX⟨2·14⟩ ; lem-comm-SWAP03-BOX⟨2·41⟩)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-perm-2134-at03102132 : Ws → St 76
  lem-box-perm-2134-at03102132 = pickᴰ 0 Sᴰ
  lem-box-tQ-at0210213443 : Ws → St 77
  lem-box-tQ-at0210213443 = pickᴰ 1 Sᴰ
  lem-box-tQ-at0213243140 : Ws → St 23
  lem-box-tQ-at0213243140 = pickᴰ 2 Sᴰ
  lem-box-tQ-at0220 : Ws → St 24
  lem-box-tQ-at0220 = pickᴰ 3 Sᴰ
  lem-box-tQ-at03102132 : Ws → St 78
  lem-box-tQ-at03102132 = pickᴰ 4 Sᴰ
  lem-box-tQ-at0410213243 : Ws → St 79
  lem-box-tQ-at0410213243 = pickᴰ 5 Sᴰ
  lem-box-tQ-at14233241 : Ws → St 30
  lem-box-tQ-at14233241 = pickᴰ 6 Sᴰ
  lem-cQ-at02102441 : Ws → St 80
  lem-cQ-at02102441 = pickᴰ 7 Sᴰ
  lem-cQ-at0213213440 : Ws → St 81
  lem-cQ-at0213213440 = pickᴰ 8 Sᴰ
  lem-cQ-at0214203143 : Ws → St 36
  lem-cQ-at0214203143 = pickᴰ 9 Sᴰ
  lem-cQ-at022330 : Ws → St 38
  lem-cQ-at022330 = pickᴰ 10 Sᴰ
  lem-cQ-at02233440 : Ws → St 82
  lem-cQ-at02233440 = pickᴰ 11 Sᴰ
  lem-cQ-at022440 : Ws → St 83
  lem-cQ-at022440 = pickᴰ 12 Sᴰ
  lem-cQ-at033440 : Ws → St 45
  lem-cQ-at033440 = pickᴰ 13 Sᴰ
  lem-cQ-at12243143 : Ws → St 51
  lem-cQ-at12243143 = pickᴰ 14 Sᴰ
  lem-cQ-at14213243 : Ws → St 57
  lem-cQ-at14213243 = pickᴰ 15 Sᴰ
  lem-cQ-at1441 : Ws → St 59
  lem-cQ-at1441 = pickᴰ 16 Sᴰ
  lem-cQ-at2442 : Ws → St 63
  lem-cQ-at2442 = pickᴰ 17 Sᴰ
  lem-tP-at021021 : Ws → St 65
  lem-tP-at021021 = pickᴰ 18 Sᴰ
  lem-tP-at0210213443 : Ws → St 66
  lem-tP-at0210213443 = pickᴰ 19 Sᴰ
  lem-tP-at0213243140 : Ws → St 84
  lem-tP-at0213243140 = pickᴰ 20 Sᴰ
  lem-tP-at03102132 : Ws → St 68
  lem-tP-at03102132 = pickᴰ 21 Sᴰ
  lem-tP-at032032 : Ws → St 69
  lem-tP-at032032 = pickᴰ 22 Sᴰ
  lem-box-perm-2134-at0210243143 : Ws → St 85
  lem-box-perm-2134-at0210243143 = pickᴰ 23 Sᴰ
  lem-box-tQ-at021021 : Ws → St 86
  lem-box-tQ-at021021 = pickᴰ 24 Sᴰ
  lem-box-tQ-at0213243041 : Ws → St 87
  lem-box-tQ-at0213243041 = pickᴰ 25 Sᴰ
  lem-box-tQ-at0214233041 : Ws → St 88
  lem-box-tQ-at0214233041 = pickᴰ 26 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 89
  lem-box-tQ-at0310213442 = pickᴰ 27 Sᴰ
  lem-cQ-at02102331 : Ws → St 90
  lem-cQ-at02102331 = pickᴰ 28 Sᴰ
  lem-cQ-at02132031 : Ws → St 91
  lem-cQ-at02132031 = pickᴰ 29 Sᴰ
  lem-cQ-at02132130 : Ws → St 92
  lem-cQ-at02132130 = pickᴰ 30 Sᴰ
  lem-cQ-at02142041 : Ws → St 93
  lem-cQ-at02142041 = pickᴰ 31 Sᴰ
  lem-cQ-at0310243241 : Ws → St 94
  lem-cQ-at0310243241 = pickᴰ 32 Sᴰ
  lem-cQ-at031031 : Ws → St 95
  lem-cQ-at031031 = pickᴰ 33 Sᴰ
  lem-cQ-at03103441 : Ws → St 96
  lem-cQ-at03103441 = pickᴰ 34 Sᴰ
  lem-cQ-at03122031 : Ws → St 97
  lem-cQ-at03122031 = pickᴰ 35 Sᴰ
  lem-cQ-at0312203441 : Ws → St 98
  lem-cQ-at0312203441 = pickᴰ 36 Sᴰ
  lem-cQ-at03122130 : Ws → St 99
  lem-cQ-at03122130 = pickᴰ 37 Sᴰ
  lem-cQ-at0312243041 : Ws → St 100
  lem-cQ-at0312243041 = pickᴰ 38 Sᴰ
  lem-cQ-at0314203241 : Ws → St 101
  lem-cQ-at0314203241 = pickᴰ 39 Sᴰ
  lem-cQ-at0314213240 : Ws → St 102
  lem-cQ-at0314213240 = pickᴰ 40 Sᴰ
  lem-cQ-at03143041 : Ws → St 103
  lem-cQ-at03143041 = pickᴰ 41 Sᴰ
  lem-cQ-at03143140 : Ws → St 104
  lem-cQ-at03143140 = pickᴰ 42 Sᴰ
  lem-cQ-at03243042 : Ws → St 105
  lem-cQ-at03243042 = pickᴰ 43 Sᴰ
  lem-cQ-at03243240 : Ws → St 106
  lem-cQ-at03243240 = pickᴰ 44 Sᴰ
  lem-cQ-at04103143 : Ws → St 107
  lem-cQ-at04103143 = pickᴰ 45 Sᴰ
  lem-cQ-at04122041 : Ws → St 108
  lem-cQ-at04122041 = pickᴰ 46 Sᴰ
  lem-cQ-at0412233041 : Ws → St 109
  lem-cQ-at0412233041 = pickᴰ 47 Sᴰ
  lem-cQ-at04233042 : Ws → St 110
  lem-cQ-at04233042 = pickᴰ 48 Sᴰ
  lem-cQ-at142142 : Ws → St 111
  lem-cQ-at142142 = pickᴰ 49 Sᴰ
  lem-tP-at0213243041 : Ws → St 112
  lem-tP-at0213243041 = pickᴰ 50 Sᴰ
  lem-tP-at0214233041 : Ws → St 113
  lem-tP-at0214233041 = pickᴰ 51 Sᴰ
  lem-tP-at0310213442 : Ws → St 114
  lem-tP-at0310213442 = pickᴰ 52 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wpE 767 c4
  q2 : Ws → Eqn
  q2 c4 = wlE 915 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CZ13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = sE 82 (lem-cQ-at02233440 c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 916 (lit c4)

-- box-tQ @02233440: 13 steps
lem-box-tQ-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at02233440 c4 = derive (Bx2-1340 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   re 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q6 : Ws → Eqn
  q6 c4 = wpE 766 c4
  q7 : Ws → Eqn
  q7 c4 = sE 81 (lem-cQ-at0213213440 c4)

-- box-tQ @0213213440: 13 steps
lem-box-tQ-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0213213440 c4 = derive (Bx2-3140 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q6 c4) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = sE 23 (lem-box-tQ-at0213243140 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 84 (lem-tP-at0213243140 c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 949 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 950 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CZ01 ∷ Toff234 ∷ []) (Toff234 ∷ CZ01 ∷ []) (c₂ (CZ) (Toff))
  q13 : Ws → Eqn
  q13 c4 = wlE 951 (lit c4)

-- P-box @0213243140: 8 steps
lem-P-box-at0213243140 : Ws → ⟪ (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-P-box-at0213243140 c4 = derive (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) (Bx2-3410 ∷ [])
  (rw 1 (q8 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 0 (q8 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = wlE 419 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 418 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS01⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS01⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS01⁻ ∷ S2 ∷ []) (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS01⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑))
  q20 : Ws → Eqn
  q20 c4 = wlE 179 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (S2 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS))
  q22 : Ws → Eqn
  q22 c4 = eqn (Toff201 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS))
  q23 : Ws → Eqn
  q23 c4 = eqn (S2⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS))

-- VPQ @0213243140: 14 steps
lem-VPQ-at0213243140 : Ws → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0213243140 c4 = derive (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 0 (q15 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = sE 24 (lem-box-tQ-at0220 c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 955 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 773 c4
  q27 : Ws → Eqn
  q27 c4 = wpE 774 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 341 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 452 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q31 : Ws → Eqn
  q31 c4 = wpE 342 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 302 c4
  q33 : Ws → Eqn
  q33 c4 = wpE 90 c4
  q34 : Ws → Eqn
  q34 c4 = wpE 775 c4
  q35 : Ws → Eqn
  q35 c4 = wpE 761 c4

-- CXbc-box @0220: 17 steps
lem-CXbc-box-at0220 : Ws → ⟪ (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0220 c4 = derive (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) (Bx2-1034 ∷ CCZ014 ∷ [])
  (rw 1 (q24 c4) ∷
   rw 0 (q25 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw 3 (q27 c4) ∷
   rw 2 (q25 c4) ∷
   rw 5 (q28 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 8 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   rw 4 (q34 c4) ∷
   rw⁻ 0 (q24 c4) ∷
   rw⁻ 1 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wlE 956 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 957 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wpE 776 c4
  q39 : Ws → Eqn
  q39 c4 = wlE 166 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 777 c4
  q41 : Ws → Eqn
  q41 c4 = wlE 958 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS))
  q43 : Ws → Eqn
  q43 c4 = wlE 921 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 959 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 960 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wpE 759 c4

-- CXcb-box @0220: 18 steps
lem-CXcb-box-at0220 : Ws → ⟪ (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at0220 c4 = derive (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) (Bx2-1034 ∷ CCZ134 ∷ [])
  (rw 1 (q24 c4) ∷
   rw 0 (q36 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw⁻ 0 (q24 c4) ∷
   rw⁻ 1 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = wlE 926 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 962 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wlE 924 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wlE 963 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (Sw03 ∷ Bx2-14 ∷ []) (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4))
  q52 : Ws → Eqn
  q52 c4 = wlE 928 (lit c4)

-- nat-SWbc @0220: 23 steps
lem-nat-SWbc-at0220 : Ws → ⟪ (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-nat-SWbc-at0220 c4 = derive (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (Bx2-1304 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) ∷
   rw⁻ 0 (q47 c4) ∷
   rw 1 (q48 c4) ∷
   re 3 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw 5 (q50 c4) ∷
   rw⁻ 6 (q49 c4) ∷
   rw 7 (q51 c4) ∷
   rw 8 (q48 c4) ∷
   rw⁻ 9 (q47 c4) ∷
   re 11 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   rw⁻ 10 (q49 c4) ∷
   rw 11 (q50 c4) ∷
   rw 12 (q51 c4) ∷
   rw 13 (q50 c4) ∷
   rw⁻ 14 (q49 c4) ∷
   rw 15 (q51 c4) ∷
   rw 16 (q52 c4) ∷
   re 2 6 (Bx1-204 ∷ []) ∷
   re 5 6 (Bx1-204 ∷ []) ∷
   re 0 6 (Bx2-1304 ∷ []) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = wlE 174 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 14 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 175 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = sE 38 (lem-cQ-at022330 c4)

-- tP @022330: 7 steps
lem-tP-at022330 : Ws → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at022330 c4 = derive (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = wpE 49 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 200 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wlE 157 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = sE 57 (lem-cQ-at14213243 c4)

-- tP @14213243: 7 steps
lem-tP-at14213243 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at14213243 c4 = derive (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q57 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw 2 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q57 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = sE 76 (lem-box-perm-2134-at03102132 c4)
  q62 : Ws → Eqn
  q62 c4 = wpE 894 c4

-- S-sym-xt: 8 steps
lem-S-sym-xt : Ws → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-02-4 ∷ []) ⟫ʷ
lem-S-sym-xt c4 = derive (Sb3-0-12-4 ∷ []) (Sb3-1-02-4 ∷ [])
  (re 0 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) ∷
   re 2 1 (CS04 ∷ []) ∷
   re 4 1 (CS04⁻ ∷ []) ∷
   rw 0 (q61 c4) ∷
   rw⁻ 1 (q62 c4) ∷
   re 2 1 (Sb3-1-4-2 ∷ []) ∷
   re 4 1 (Sb⁻3-1-4-2 ∷ []) ∷
   re 0 5 (Sb3-1-02-4 ∷ []) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = sE 78 (lem-box-tQ-at03102132 c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 524 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 1097 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wpE 895 c4
  q67 : Ws → Eqn
  q67 c4 = wpE 301 c4
  q68 : Ws → Eqn
  q68 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q69 : Ws → Eqn
  q69 c4 = wlE 451 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 1098 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wpE 655 c4

-- CXbc-box @03102132: 17 steps
lem-CXbc-box-at03102132 : Ws → ⟪ (CX12 ∷ Bx3-0124 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at03102132 c4 = derive (CX12 ∷ Bx3-0124 ∷ CX12 ∷ []) (Bx3-0124 ∷ CCZ014 ∷ [])
  (rw 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 3 (q66 c4) ∷
   rw 2 (q64 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 8 (q68 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   rw 4 (q45 c4) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 4 (q70 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw⁻ 1 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = wlE 1099 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = wpE 896 c4
  q74 : Ws → Eqn
  q74 c4 = wlE 836 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = wpE 296 c4
  q76 : Ws → Eqn
  q76 c4 = wpE 897 c4
  q77 : Ws → Eqn
  q77 c4 = wlE 521 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CS24⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CS24 ∷ Toff301 ∷ []) (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = wlE 1100 (lit c4)
  q81 : Ws → Eqn
  q81 c4 = wlE 1101 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wpE 898 c4

-- CXcb-box @03102132: 18 steps
lem-CXcb-box-at03102132 : Ws → ⟪ (CX21 ∷ Bx3-0124 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at03102132 c4 = derive (CX21 ∷ Bx3-0124 ∷ CX21 ∷ []) (Bx3-0124 ∷ CCZ024 ∷ [])
  (rw 1 (q63 c4) ∷
   rw 0 (q72 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw 7 (q77 c4) ∷
   rw 6 (q78 c4) ∷
   rw 5 (q77 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   rw⁻ 3 (q80 c4) ∷
   rw 2 (q72 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw⁻ 1 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = sE 36 (lem-cQ-at0214203143 c4)

-- tP @0214203143: 7 steps
lem-tP-at0214203143 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at0214203143 c4 = derive (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q83 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q54 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = wlE 624 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 625 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = sE 83 (lem-cQ-at022440 c4)

-- tP @022440: 7 steps
lem-tP-at022440 : Ws → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at022440 c4 = derive (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  (rw⁻ 0 (q84 c4) ∷
   rw⁻ 3 (q85 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q86 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q84 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = wlE 1126 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = wlE 622 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CZ14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = wlE 623 (lit c4)

-- box-tQ @022440: 13 steps
lem-box-tQ-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at022440 c4 = derive (Bx2-1430 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q87 c4) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q87 c4) ∷
   rw 0 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q90 c4) ∷ []) Eq.refl

-- tP @02233440: 7 steps
lem-tP-at02233440 : Ws → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at02233440 c4 = derive (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = wpE 78 c4
  q92 : Ws → Eqn
  q92 c4 = wlE 226 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = sE 59 (lem-cQ-at1441 c4)

-- tP @1441: 7 steps
lem-tP-at1441 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at1441 c4 = derive (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q91 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw 2 (q59 c4) ∷
   rw 1 (q93 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q91 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = sE 80 (lem-cQ-at02102441 c4)

-- tP @02102441: 7 steps
lem-tP-at02102441 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at02102441 c4 = derive (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q94 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q54 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = wlE 1155 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = wpE 25 c4
  q97 : Ws → Eqn
  q97 c4 = eqn (CZ04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = wpE 26 c4

-- box-tQ @02102441: 13 steps
lem-box-tQ-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at02102441 c4 = derive (Bx2-0431 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q95 c4) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q95 c4) ∷
   rw 0 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = sE 63 (lem-cQ-at2442 c4)

-- tP @2442: 7 steps
lem-tP-at2442 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at2442 c4 = derive (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q57 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw 2 (q59 c4) ∷
   rw 1 (q99 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q57 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = sE 51 (lem-cQ-at12243143 c4)

-- tP @12243143: 7 steps
lem-tP-at12243143 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at12243143 c4 = derive (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  (rw⁻ 0 (q91 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw 2 (q59 c4) ∷
   rw 1 (q100 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q91 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = sE 30 (lem-box-tQ-at14233241 c4)
  q102 : Ws → Eqn
  q102 c4 = wpE 172 c4
  q103 : Ws → Eqn
  q103 c4 = wlE 1174 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wpE 771 c4
  q105 : Ws → Eqn
  q105 c4 = wlE 707 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wpE 11 c4
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ012 ∷ CX43 ∷ []) (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀))
  q108 : Ws → Eqn
  q108 c4 = wlE 992 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 311 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 704 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wlE 1175 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = wlE 254 (lit c4)

-- CXbc-box @14233241: 17 steps
lem-CXbc-box-at14233241 : Ws → ⟪ (CX32 ∷ Bx0-4321 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at14233241 c4 = derive (CX32 ∷ Bx0-4321 ∷ CX32 ∷ []) (Bx0-4321 ∷ CCZ134 ∷ [])
  (rw 1 (q101 c4) ∷
   rw 0 (q102 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw 3 (q104 c4) ∷
   rw 2 (q102 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 9 (q106 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw⁻ 6 (q107 c4) ∷
   rw⁻ 5 (q109 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw⁻ 3 (q103 c4) ∷
   rw 4 (q111 c4) ∷
   rw⁻ 0 (q101 c4) ∷
   rw⁻ 1 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = wpE 983 c4
  q114 : Ws → Eqn
  q114 c4 = wpE 984 c4
  q115 : Ws → Eqn
  q115 c4 = wlE 411 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = wlE 702 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = wpE 251 c4
  q118 : Ws → Eqn
  q118 c4 = wpE 163 c4
  q119 : Ws → Eqn
  q119 c4 = eqn (CS12⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (CS12 ∷ Toff034 ∷ []) (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = wpE 591 c4
  q122 : Ws → Eqn
  q122 c4 = wpE 985 c4
  q123 : Ws → Eqn
  q123 c4 = wpE 205 c4
  q124 : Ws → Eqn
  q124 c4 = wlE 257 (lit c4)

-- CXcb-box @14233241: 18 steps
lem-CXcb-box-at14233241 : Ws → ⟪ (CX23 ∷ Bx0-4321 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at14233241 c4 = derive (CX23 ∷ Bx0-4321 ∷ CX23 ∷ []) (Bx0-4321 ∷ CCZ124 ∷ [])
  (rw 1 (q101 c4) ∷
   rw 0 (q113 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw⁻ 1 (q115 c4) ∷
   rw 4 (q116 c4) ∷
   rw 8 (q117 c4) ∷
   rw 7 (q118 c4) ∷
   rw 6 (q119 c4) ∷
   rw 5 (q118 c4) ∷
   rw 4 (q120 c4) ∷
   rw⁻ 5 (q116 c4) ∷
   rw 3 (q121 c4) ∷
   rw 2 (q113 c4) ∷
   rw 3 (q122 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw⁻ 0 (q101 c4) ∷
   rw⁻ 1 (q124 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = wpE 988 c4
  q126 : Ws → Eqn
  q126 c4 = wlE 846 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CZ24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = sE 104 (lem-cQ-at03143140 c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 847 (lit c4)

-- box-tQ @03143140: 13 steps
lem-box-tQ-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at03143140 c4 = derive (Bx3-4210 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw⁻ 2 (q125 c4) ∷
   re 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw⁻ 5 (q125 c4) ∷
   rw 0 (q126 c4) ∷
   rw 2 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q129 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = wlE 781 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = wlE 782 (lit c4)
  q132 : Ws → Eqn
  q132 c4 = wlE 436 (lit c4)
  q133 : Ws → Eqn
  q133 c4 = sE 102 (lem-cQ-at0314213240 c4)

-- tP @0314213240: 7 steps
lem-tP-at0314213240 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at0314213240 c4 = derive (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q130 c4) ∷
   rw⁻ 3 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q131 c4) ∷
   rw 1 (q130 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = wlE 749 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = sE 106 (lem-cQ-at03243240 c4)
  q136 : Ws → Eqn
  q136 c4 = wlE 750 (lit c4)

-- box-tQ @03243240: 13 steps
lem-box-tQ-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at03243240 c4 = derive (Bx3-1420 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q87 c4) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q87 c4) ∷
   rw 0 (q134 c4) ∷
   rw 2 (q89 c4) ∷
   rw 1 (q135 c4) ∷
   rw 2 (q136 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = wpE 992 c4

-- box-tQ @0314213240: 13 steps
lem-box-tQ-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw⁻ 2 (q137 c4) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw⁻ 5 (q137 c4) ∷
   rw 0 (q134 c4) ∷
   rw 2 (q89 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q136 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = wlE 435 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = wlE 434 (lit c4)

-- tP @03143140: 7 steps
lem-tP-at03143140 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at03143140 c4 = derive (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  (rw⁻ 0 (q138 c4) ∷
   rw⁻ 3 (q139 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q128 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q139 c4) ∷
   rw 1 (q138 c4) ∷ []) Eq.refl

-- tP @03243240: 7 steps
lem-tP-at03243240 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at03243240 c4 = derive (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q130 c4) ∷
   rw⁻ 3 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q135 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q131 c4) ∷
   rw 1 (q130 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = wlE 487 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = wpE 343 c4
  q142 : Ws → Eqn
  q142 c4 = sE 45 (lem-cQ-at033440 c4)

-- tP @033440: 7 steps
lem-tP-at033440 : Ws → ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-tP-at033440 c4 = derive (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q140 c4) ∷
   rw⁻ 3 (q141 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q142 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q140 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = wpE 1048 c4
  q144 : Ws → Eqn
  q144 c4 = wlE 1238 (lit c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (CZ02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = sE 96 (lem-cQ-at03103441 c4)
  q147 : Ws → Eqn
  q147 c4 = wlE 1239 (lit c4)

-- box-tQ @03103441: 13 steps
lem-box-tQ-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at03103441 c4 = derive (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q143 c4) ∷
   re 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q143 c4) ∷
   rw 0 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q147 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = sE 94 (lem-cQ-at0310243241 c4)

-- tP @0310243241: 7 steps
lem-tP-at0310243241 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0310243241 c4 = derive (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q141 c4) ∷
   rw⁻ 3 (q140 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q148 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = wpE 353 c4
  q150 : Ws → Eqn
  q150 c4 = wpE 354 c4

-- box-tQ @0310243241: 13 steps
lem-box-tQ-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0310243241 c4 = derive (Bx3-0421 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q95 c4) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q95 c4) ∷
   rw 0 (q149 c4) ∷
   rw 2 (q97 c4) ∷
   rw 1 (q148 c4) ∷
   rw 2 (q150 c4) ∷ []) Eq.refl

-- tP @03103441: 7 steps
lem-tP-at03103441 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at03103441 c4 = derive (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q131 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q146 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = sE 89 (lem-box-tQ-at0310213442 c4)
  q152 : Ws → Eqn
  q152 c4 = wpE 1069 c4
  q153 : Ws → Eqn
  q153 c4 = wlE 1257 (lit c4)
  q154 : Ws → Eqn
  q154 c4 = wlE 1258 (lit c4)
  q155 : Ws → Eqn
  q155 c4 = wlE 348 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = wpE 279 c4
  q157 : Ws → Eqn
  q157 c4 = wlE 414 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = wlE 415 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wlE 508 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = wlE 1259 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = wpE 728 c4

-- CXbc-box @0310213442: 17 steps
lem-CXbc-box-at0310213442 : Ws → ⟪ (CX14 ∷ Bx3-0142 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0310213442 c4 = derive (CX14 ∷ Bx3-0142 ∷ CX14 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  (rw 1 (q151 c4) ∷
   rw 0 (q152 c4) ∷
   rw⁻ 1 (q153 c4) ∷
   rw 3 (q154 c4) ∷
   rw 2 (q152 c4) ∷
   rw 5 (q155 c4) ∷
   rw⁻ 9 (q156 c4) ∷
   rw 8 (q68 c4) ∷
   rw⁻ 7 (q157 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 5 (q158 c4) ∷
   rw⁻ 6 (q155 c4) ∷
   rw 4 (q159 c4) ∷
   rw⁻ 3 (q153 c4) ∷
   rw 4 (q160 c4) ∷
   rw⁻ 0 (q151 c4) ∷
   rw⁻ 1 (q161 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = wpE 1070 c4
  q163 : Ws → Eqn
  q163 c4 = wpE 1071 c4
  q164 : Ws → Eqn
  q164 c4 = wlE 302 (lit c4)
  q165 : Ws → Eqn
  q165 c4 = wpE 13 c4
  q166 : Ws → Eqn
  q166 c4 = wlE 1260 (lit c4)
  q167 : Ws → Eqn
  q167 c4 = wpE 1072 c4
  q168 : Ws → Eqn
  q168 c4 = wpE 1066 c4
  q169 : Ws → Eqn
  q169 c4 = wpE 1073 c4
  q170 : Ws → Eqn
  q170 c4 = wpE 727 c4

-- CXcb-box @0310213442: 18 steps
lem-CXcb-box-at0310213442 : Ws → ⟪ (CX41 ∷ Bx3-0142 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0310213442 c4 = derive (CX41 ∷ Bx3-0142 ∷ CX41 ∷ []) (Bx3-0142 ∷ CCZ024 ∷ [])
  (rw 1 (q151 c4) ∷
   rw 0 (q162 c4) ∷
   rw⁻ 2 (q163 c4) ∷
   rw⁻ 1 (q164 c4) ∷
   rw 4 (q165 c4) ∷
   rw 8 (q166 c4) ∷
   rw 7 (q167 c4) ∷
   rw 6 (q78 c4) ∷
   rw 5 (q167 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   rw⁻ 3 (q168 c4) ∷
   rw 2 (q162 c4) ∷
   rw 3 (q169 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 3 (q164 c4) ∷
   rw⁻ 0 (q151 c4) ∷
   rw⁻ 1 (q170 c4) ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = wlE 1271 (lit c4)
  q172 : Ws → Eqn
  q172 c4 = sE 98 (lem-cQ-at0312203441 c4)

-- box-tQ @0312203441: 13 steps
lem-box-tQ-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at0312203441 c4 = derive (Bx3-2041 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q171 c4) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q171 c4) ∷
   rw 0 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q172 c4) ∷
   rw 2 (q147 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = sE 100 (lem-cQ-at0312243041 c4)

-- tP @0312243041: 7 steps
lem-tP-at0312243041 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at0312243041 c4 = derive (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  (rw⁻ 0 (q138 c4) ∷
   rw⁻ 3 (q139 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q173 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q139 c4) ∷
   rw 1 (q138 c4) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = wlE 231 (lit c4)

-- box-tQ @0312243041: 13 steps
lem-box-tQ-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at0312243041 c4 = derive (Bx3-2401 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q174 c4) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q174 c4) ∷
   rw 0 (q126 c4) ∷
   rw 2 (q127 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q129 c4) ∷ []) Eq.refl

-- tP @0312203441: 7 steps
lem-tP-at0312203441 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at0312203441 c4 = derive (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q131 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q172 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = wlE 1303 (lit c4)
  q176 : Ws → Eqn
  q176 c4 = sE 97 (lem-cQ-at03122031 c4)

-- box-tQ @03122031: 13 steps
lem-box-tQ-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at03122031 c4 = derive (Bx3-2014 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q175 c4) ∷
   re 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q175 c4) ∷
   rw 0 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q147 c4) ∷ []) Eq.refl

private
  q177 : Ws → Eqn
  q177 c4 = wpE 262 c4
  q178 : Ws → Eqn
  q178 c4 = sE 95 (lem-cQ-at031031 c4)

-- box-tQ @031031: 13 steps
lem-box-tQ-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at031031 c4 = derive (Bx3-0214 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q177 c4) ∷
   re 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q177 c4) ∷
   rw 0 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q178 c4) ∷
   rw 2 (q147 c4) ∷ []) Eq.refl

-- tP @031031: 7 steps
lem-tP-at031031 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at031031 c4 = derive (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q131 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q178 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = sE 68 (lem-tP-at03102132 c4)
  q180 : Ws → Eqn
  q180 c4 = wlE 842 (lit c4)
  q181 : Ws → Eqn
  q181 c4 = wlE 843 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (CZ24 ∷ Toff301 ∷ []) (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = wlE 844 (lit c4)

-- P-box @03102132: 8 steps
lem-P-box-at03102132 : Ws → ⟪ (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-P-box-at03102132 c4 = derive (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ [])
  (rw 1 (q63 c4) ∷
   rw⁻ 0 (q179 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw⁻ 3 (q179 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 2 (q182 c4) ∷
   rw⁻ 3 (q183 c4) ∷
   rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = wpE 214 c4
  q185 : Ws → Eqn
  q185 c4 = sE 103 (lem-cQ-at03143041 c4)

-- box-tQ @03143041: 13 steps
lem-box-tQ-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at03143041 c4 = derive (Bx3-4201 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q184 c4) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q184 c4) ∷
   rw 0 (q126 c4) ∷
   rw 2 (q127 c4) ∷
   rw 1 (q185 c4) ∷
   rw 2 (q129 c4) ∷ []) Eq.refl

private
  q186 : Ws → Eqn
  q186 c4 = wlE 1319 (lit c4)
  q187 : Ws → Eqn
  q187 c4 = sE 101 (lem-cQ-at0314203241 c4)

-- box-tQ @0314203241: 13 steps
lem-box-tQ-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q186 c4) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q186 c4) ∷
   rw 0 (q149 c4) ∷
   rw 2 (q97 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q150 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = sE 93 (lem-cQ-at02142041 c4)

-- box-tQ @02142041: 13 steps
lem-box-tQ-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at02142041 c4 = derive (Bx2-4031 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q186 c4) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q186 c4) ∷
   rw 0 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q98 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = wpE 1155 c4
  q190 : Ws → Eqn
  q190 c4 = wpE 1156 c4
  q191 : Ws → Eqn
  q191 c4 = wpE 1157 c4
  q192 : Ws → Eqn
  q192 c4 = wpE 1158 c4
  q193 : Ws → Eqn
  q193 c4 = eqn (Sw03 ∷ Bx2-41 ∷ []) (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4))

-- nat-SWbc @02142041: 23 steps
lem-nat-SWbc-at02142041 : Ws → ⟪ (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-nat-SWbc-at02142041 c4 = derive (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (Bx2-4301 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) ∷
   rw⁻ 0 (q189 c4) ∷
   rw 1 (q190 c4) ∷
   re 3 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   rw⁻ 2 (q191 c4) ∷
   rw 3 (q192 c4) ∷
   rw 4 (q193 c4) ∷
   rw 5 (q192 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 7 (q193 c4) ∷
   rw 8 (q190 c4) ∷
   rw⁻ 9 (q189 c4) ∷
   re 11 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   rw⁻ 10 (q191 c4) ∷
   rw 11 (q192 c4) ∷
   rw 12 (q193 c4) ∷
   rw 13 (q192 c4) ∷
   rw⁻ 14 (q191 c4) ∷
   rw 15 (q193 c4) ∷
   rw 16 (q52 c4) ∷
   re 2 6 (Bx4-201 ∷ []) ∷
   re 5 6 (Bx4-201 ∷ []) ∷
   re 0 6 (Bx2-4301 ∷ []) ∷ []) Eq.refl

private
  q194 : Ws → Eqn
  q194 c4 = sE 113 (lem-tP-at0214233041 c4)

-- VPQ @0214233041: 14 steps
lem-VPQ-at0214233041 : Ws → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0214233041 c4 = derive (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw 3 (q194 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 0 (q15 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = sE 88 (lem-box-tQ-at0214233041 c4)

-- P-box @0214233041: 8 steps
lem-P-box-at0214233041 : Ws → ⟪ (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-P-box-at0214233041 c4 = derive (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) (Bx2-4301 ∷ [])
  (rw 1 (q195 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 3 (q194 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 0 (q195 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = sE 77 (lem-box-tQ-at0210213443 c4)
  q197 : Ws → Eqn
  q197 c4 = wpE 1164 c4
  q198 : Ws → Eqn
  q198 c4 = wlE 1328 (lit c4)
  q199 : Ws → Eqn
  q199 c4 = wlE 184 (lit c4)
  q200 : Ws → Eqn
  q200 c4 = wpE 294 c4
  q201 : Ws → Eqn
  q201 c4 = wlE 432 (lit c4)
  q202 : Ws → Eqn
  q202 c4 = wlE 433 (lit c4)
  q203 : Ws → Eqn
  q203 c4 = wpE 565 c4

-- CXbc-box @0210213443: 17 steps
lem-CXbc-box-at0210213443 : Ws → ⟪ (CX14 ∷ Bx2-0143 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0210213443 c4 = derive (CX14 ∷ Bx2-0143 ∷ CX14 ∷ []) (Bx2-0143 ∷ CCZ013 ∷ [])
  (rw 1 (q196 c4) ∷
   rw 0 (q197 c4) ∷
   rw⁻ 1 (q153 c4) ∷
   rw 3 (q198 c4) ∷
   rw 2 (q197 c4) ∷
   rw 5 (q199 c4) ∷
   rw⁻ 9 (q200 c4) ∷
   rw 8 (q68 c4) ∷
   rw⁻ 7 (q201 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 5 (q202 c4) ∷
   rw⁻ 6 (q199 c4) ∷
   rw 4 (q159 c4) ∷
   rw⁻ 3 (q153 c4) ∷
   rw 4 (q160 c4) ∷
   rw⁻ 0 (q196 c4) ∷
   rw⁻ 1 (q203 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = wpE 1165 c4
  q205 : Ws → Eqn
  q205 c4 = wpE 1166 c4
  q206 : Ws → Eqn
  q206 c4 = wpE 352 c4
  q207 : Ws → Eqn
  q207 c4 = wlE 1329 (lit c4)
  q208 : Ws → Eqn
  q208 c4 = wpE 1167 c4
  q209 : Ws → Eqn
  q209 c4 = wpE 563 c4
  q210 : Ws → Eqn
  q210 c4 = wpE 1168 c4
  q211 : Ws → Eqn
  q211 c4 = wpE 129 c4
  q212 : Ws → Eqn
  q212 c4 = wpE 560 c4

-- CXcb-box @0210213443: 18 steps
lem-CXcb-box-at0210213443 : Ws → ⟪ (CX41 ∷ Bx2-0143 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0210213443 c4 = derive (CX41 ∷ Bx2-0143 ∷ CX41 ∷ []) (Bx2-0143 ∷ CCZ034 ∷ [])
  (rw 1 (q196 c4) ∷
   rw 0 (q204 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw⁻ 1 (q164 c4) ∷
   rw 4 (q206 c4) ∷
   rw 8 (q207 c4) ∷
   rw 7 (q208 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 5 (q208 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 5 (q206 c4) ∷
   rw⁻ 3 (q209 c4) ∷
   rw 2 (q204 c4) ∷
   rw 3 (q210 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 3 (q164 c4) ∷
   rw⁻ 0 (q196 c4) ∷
   rw⁻ 1 (q212 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = sE 66 (lem-tP-at0210213443 c4)
  q214 : Ws → Eqn
  q214 c4 = wlE 932 (lit c4)
  q215 : Ws → Eqn
  q215 c4 = wlE 933 (lit c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (Toff201 ∷ CZ34 ∷ []) (CZ34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CZ))
  q217 : Ws → Eqn
  q217 c4 = wlE 934 (lit c4)

-- P-box @0210213443: 8 steps
lem-P-box-at0210213443 : Ws → ⟪ (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-P-box-at0210213443 c4 = derive (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) (Bx2-0143 ∷ [])
  (rw 1 (q196 c4) ∷
   rw⁻ 0 (q213 c4) ∷
   rw⁻ 1 (q214 c4) ∷
   rw⁻ 3 (q213 c4) ∷
   rw⁻ 4 (q215 c4) ∷
   rw⁻ 2 (q216 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw⁻ 0 (q196 c4) ∷ []) Eq.refl

private
  q218 : Ws → Eqn
  q218 c4 = wpE 1175 c4
  q219 : Ws → Eqn
  q219 c4 = wlE 383 (lit c4)
  q220 : Ws → Eqn
  q220 c4 = wlE 426 (lit c4)
  q221 : Ws → Eqn
  q221 c4 = wlE 298 (lit c4)
  q222 : Ws → Eqn
  q222 c4 = wlE 384 (lit c4)

-- CXbc-box @0214233041: 17 steps
lem-CXbc-box-at0214233041 : Ws → ⟪ (CX30 ∷ Bx2-4301 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at0214233041 c4 = derive (CX30 ∷ Bx2-4301 ∷ CX30 ∷ []) (Bx2-4301 ∷ CCZ134 ∷ [])
  (rw 1 (q195 c4) ∷
   rw 0 (q218 c4) ∷
   rw⁻ 1 (q219 c4) ∷
   rw 3 (q220 c4) ∷
   rw 2 (q218 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 9 (q106 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw⁻ 6 (q107 c4) ∷
   rw⁻ 5 (q109 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw⁻ 4 (q221 c4) ∷
   rw⁻ 3 (q219 c4) ∷
   rw 4 (q222 c4) ∷
   rw⁻ 0 (q195 c4) ∷
   rw⁻ 1 (q46 c4) ∷ []) Eq.refl

private
  q223 : Ws → Eqn
  q223 c4 = wpE 1176 c4
  q224 : Ws → Eqn
  q224 c4 = wpE 1177 c4
  q225 : Ws → Eqn
  q225 c4 = wlE 381 (lit c4)
  q226 : Ws → Eqn
  q226 c4 = wpE 1143 c4
  q227 : Ws → Eqn
  q227 c4 = wlE 1332 (lit c4)
  q228 : Ws → Eqn
  q228 c4 = wpE 1178 c4
  q229 : Ws → Eqn
  q229 c4 = eqn (CS01 ∷ Toff234 ∷ []) (Toff234 ∷ CS01 ∷ []) (c₂ (CS) (Toff))
  q230 : Ws → Eqn
  q230 c4 = wpE 1153 c4
  q231 : Ws → Eqn
  q231 c4 = wpE 1179 c4
  q232 : Ws → Eqn
  q232 c4 = wpE 167 c4

-- CXcb-box @0214233041: 18 steps
lem-CXcb-box-at0214233041 : Ws → ⟪ (CX03 ∷ Bx2-4301 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0214233041 c4 = derive (CX03 ∷ Bx2-4301 ∷ CX03 ∷ []) (Bx2-4301 ∷ CCZ014 ∷ [])
  (rw 1 (q195 c4) ∷
   rw 0 (q223 c4) ∷
   rw⁻ 2 (q224 c4) ∷
   rw⁻ 1 (q225 c4) ∷
   rw 4 (q226 c4) ∷
   rw 8 (q227 c4) ∷
   rw 7 (q228 c4) ∷
   rw 6 (q17 c4) ∷
   rw 5 (q228 c4) ∷
   rw 4 (q229 c4) ∷
   rw⁻ 5 (q226 c4) ∷
   rw 3 (q230 c4) ∷
   rw 2 (q223 c4) ∷
   rw 3 (q231 c4) ∷
   rw⁻ 4 (q232 c4) ∷
   rw⁻ 3 (q225 c4) ∷
   rw⁻ 0 (q195 c4) ∷
   rw⁻ 1 (q35 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = wpE 1180 c4
  q234 : Ws → Eqn
  q234 c4 = wpE 1181 c4

-- nat-SWbc @0214233041: 23 steps
lem-nat-SWbc-at0214233041 : Ws → ⟪ (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214233041 c4 = derive (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (Bx2-4031 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) ∷
   rw⁻ 0 (q191 c4) ∷
   rw 1 (q233 c4) ∷
   re 3 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   rw⁻ 2 (q189 c4) ∷
   rw 3 (q234 c4) ∷
   rw 4 (q193 c4) ∷
   rw 5 (q234 c4) ∷
   rw⁻ 6 (q189 c4) ∷
   rw 7 (q193 c4) ∷
   rw 8 (q233 c4) ∷
   rw⁻ 9 (q191 c4) ∷
   re 11 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   rw⁻ 10 (q189 c4) ∷
   rw 11 (q234 c4) ∷
   rw 12 (q193 c4) ∷
   rw 13 (q234 c4) ∷
   rw⁻ 14 (q189 c4) ∷
   rw 15 (q193 c4) ∷
   rw 16 (q52 c4) ∷
   re 2 6 (Bx4-231 ∷ []) ∷
   re 5 6 (Bx4-231 ∷ []) ∷
   re 0 6 (Bx2-4031 ∷ []) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = wpE 131 c4
  q236 : Ws → Eqn
  q236 c4 = sE 92 (lem-cQ-at02132130 c4)

-- box-tQ @02132130: 13 steps
lem-box-tQ-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at02132130 c4 = derive (Bx2-3104 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q235 c4) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q235 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q236 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

-- tP @03143041: 7 steps
lem-tP-at03143041 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at03143041 c4 = derive (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  (rw⁻ 0 (q138 c4) ∷
   rw⁻ 3 (q139 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q185 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q139 c4) ∷
   rw 1 (q138 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = sE 91 (lem-cQ-at02132031 c4)

-- tP @02132031: 7 steps
lem-tP-at02132031 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at02132031 c4 = derive (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q237 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷ []) Eq.refl

private
  q238 : Ws → Eqn
  q238 c4 = sE 114 (lem-tP-at0310213442 c4)

-- P-box @0310213442: 8 steps
lem-P-box-at0310213442 : Ws → ⟪ (Toff324 ∷ Bx3-0142 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-P-box-at0310213442 c4 = derive (Toff324 ∷ Bx3-0142 ∷ Toff324 ∷ []) (Bx3-0142 ∷ [])
  (rw 1 (q151 c4) ∷
   rw⁻ 0 (q238 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 2 (q182 c4) ∷
   rw⁻ 3 (q183 c4) ∷
   rw⁻ 0 (q151 c4) ∷ []) Eq.refl

private
  q239 : Ws → Eqn
  q239 c4 = wlE 437 (lit c4)
  q240 : Ws → Eqn
  q240 c4 = wlE 438 (lit c4)
  q241 : Ws → Eqn
  q241 c4 = wlE 439 (lit c4)
  q242 : Ws → Eqn
  q242 c4 = eqn (Toff301 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff301 ∷ []) (lem-comm-TOFF301-CSd24 (lit c4))
  q243 : Ws → Eqn
  q243 c4 = wlE 440 (lit c4)
  q244 : Ws → Eqn
  q244 c4 = eqn (CS01⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q245 : Ws → Eqn
  q245 c4 = wlE 441 (lit c4)
  q246 : Ws → Eqn
  q246 c4 = eqn (CS01⁻ ∷ S3 ∷ []) (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑))
  q247 : Ws → Eqn
  q247 c4 = eqn (CS01⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))
  q248 : Ws → Eqn
  q248 c4 = eqn (CS01⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑))

-- VPQ @0310213442: 14 steps
lem-VPQ-at0310213442 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at0310213442 c4 = derive (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  (rw⁻ 0 (q239 c4) ∷
   rw⁻ 4 (q240 c4) ∷
   rw⁻ 3 (q241 c4) ∷
   rw 2 (q242 c4) ∷
   rw⁻ 1 (q243 c4) ∷
   rw 0 (q244 c4) ∷
   rw 4 (q245 c4) ∷
   rw 3 (q238 c4) ∷
   rw⁻ 4 (q245 c4) ∷
   rw 1 (q246 c4) ∷
   rw 2 (q247 c4) ∷
   rw 3 (q248 c4) ∷
   rw 0 (q240 c4) ∷
   rw 2 (q239 c4) ∷ []) Eq.refl

private
  q249 : Ws → Eqn
  q249 c4 = wlE 1341 (lit c4)
  q250 : Ws → Eqn
  q250 c4 = wlE 640 (lit c4)
  q251 : Ws → Eqn
  q251 c4 = eqn (CZ03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4))
  q252 : Ws → Eqn
  q252 c4 = wlE 641 (lit c4)

-- box-tQ @02132031: 13 steps
lem-box-tQ-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at02132031 c4 = derive (Bx2-3014 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q249 c4) ∷
   re 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q249 c4) ∷
   rw 0 (q250 c4) ∷
   rw 2 (q251 c4) ∷
   rw 1 (q237 c4) ∷
   rw 2 (q252 c4) ∷ []) Eq.refl

-- tP @02132130: 7 steps
lem-tP-at02132130 : Ws → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at02132130 c4 = derive (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  (rw⁻ 0 (q53 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q236 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q53 c4) ∷ []) Eq.refl

private
  q253 : Ws → Eqn
  q253 c4 = sE 112 (lem-tP-at0213243041 c4)

-- VPQ @0213243041: 14 steps
lem-VPQ-at0213243041 : Ws → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0213243041 c4 = derive (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw 3 (q253 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 0 (q15 c4) ∷
   rw 2 (q14 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = sE 87 (lem-box-tQ-at0213243041 c4)

-- P-box @0213243041: 8 steps
lem-P-box-at0213243041 : Ws → ⟪ (Toff201 ∷ Bx2-3401 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-P-box-at0213243041 c4 = derive (Toff201 ∷ Bx2-3401 ∷ Toff201 ∷ []) (Bx2-3401 ∷ [])
  (rw 1 (q254 c4) ∷
   rw⁻ 0 (q253 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 3 (q253 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 0 (q254 c4) ∷ []) Eq.refl

private
  q255 : Ws → Eqn
  q255 c4 = wpE 111 c4
  q256 : Ws → Eqn
  q256 c4 = wlE 473 (lit c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4))
  q258 : Ws → Eqn
  q258 c4 = sE 99 (lem-cQ-at03122130 c4)
  q259 : Ws → Eqn
  q259 c4 = wlE 474 (lit c4)

-- box-tQ @03122130: 13 steps
lem-box-tQ-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at03122130 c4 = derive (Bx3-2104 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q255 c4) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q255 c4) ∷
   rw 0 (q256 c4) ∷
   rw 2 (q257 c4) ∷
   rw 1 (q258 c4) ∷
   rw 2 (q259 c4) ∷ []) Eq.refl

private
  q260 : Ws → Eqn
  q260 c4 = sE 86 (lem-box-tQ-at021021 c4)
  q261 : Ws → Eqn
  q261 c4 = sE 65 (lem-tP-at021021 c4)

-- P-box @021021: 8 steps
lem-P-box-at021021 : Ws → ⟪ (Toff234 ∷ Bx2-0134 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-P-box-at021021 c4 = derive (Toff234 ∷ Bx2-0134 ∷ Toff234 ∷ []) (Bx2-0134 ∷ [])
  (rw 1 (q260 c4) ∷
   rw⁻ 0 (q261 c4) ∷
   rw⁻ 1 (q214 c4) ∷
   rw⁻ 3 (q261 c4) ∷
   rw⁻ 4 (q215 c4) ∷
   rw⁻ 2 (q216 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw⁻ 0 (q260 c4) ∷ []) Eq.refl

-- tP @03122031: 7 steps
lem-tP-at03122031 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at03122031 c4 = derive (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  (rw⁻ 0 (q131 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q176 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷ []) Eq.refl

-- tP @03122130: 7 steps
lem-tP-at03122130 : Ws → ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-tP-at03122130 c4 = derive (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q140 c4) ∷
   rw⁻ 3 (q141 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q258 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q140 c4) ∷ []) Eq.refl

private
  q262 : Ws → Eqn
  q262 c4 = wlE 1370 (lit c4)
  q263 : Ws → Eqn
  q263 c4 = eqn (CZ01 ∷ Toff324 ∷ []) (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))
  q264 : Ws → Eqn
  q264 c4 = wlE 1192 (lit c4)

-- t-cP @03102132: 5 steps
lem-t-cP-at03102132 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-t-cP-at03102132 c4 = derive (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q262 c4) ∷
   rw 2 (q263 c4) ∷
   rw 1 (q179 c4) ∷
   rw⁻ 2 (q264 c4) ∷
   rw 3 (q179 c4) ∷ []) Eq.refl

-- tP @02142041: 7 steps
lem-tP-at02142041 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at02142041 c4 = derive (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q54 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q188 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q54 c4) ∷ []) Eq.refl

-- tP @0314203241: 7 steps
lem-tP-at0314203241 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0314203241 c4 = derive (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q141 c4) ∷
   rw⁻ 3 (q140 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q187 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = wlE 1388 (lit c4)
  q266 : Ws → Eqn
  q266 c4 = wpE 1223 c4
  q267 : Ws → Eqn
  q267 c4 = wlE 527 (lit c4)
  q268 : Ws → Eqn
  q268 c4 = wlE 1389 (lit c4)
  q269 : Ws → Eqn
  q269 c4 = wpE 1226 c4

-- CXbc-box @021021: 17 steps
lem-CXbc-box-at021021 : Ws → ⟪ (CX13 ∷ Bx2-0134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at021021 c4 = derive (CX13 ∷ Bx2-0134 ∷ CX13 ∷ []) (Bx2-0134 ∷ CCZ014 ∷ [])
  (rw 1 (q260 c4) ∷
   rw 0 (q41 c4) ∷
   rw⁻ 1 (q265 c4) ∷
   rw 3 (q266 c4) ∷
   rw 2 (q41 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw 8 (q68 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   rw 4 (q267 c4) ∷
   rw⁻ 3 (q265 c4) ∷
   rw 4 (q268 c4) ∷
   rw⁻ 0 (q260 c4) ∷
   rw⁻ 1 (q269 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = wlE 1390 (lit c4)
  q271 : Ws → Eqn
  q271 c4 = wpE 1227 c4
  q272 : Ws → Eqn
  q272 c4 = wlE 336 (lit c4)
  q273 : Ws → Eqn
  q273 c4 = wpE 231 c4
  q274 : Ws → Eqn
  q274 c4 = wpE 1187 c4
  q275 : Ws → Eqn
  q275 c4 = wlE 1391 (lit c4)
  q276 : Ws → Eqn
  q276 c4 = wlE 1392 (lit c4)
  q277 : Ws → Eqn
  q277 c4 = wpE 1228 c4

-- CXcb-box @021021: 18 steps
lem-CXcb-box-at021021 : Ws → ⟪ (CX31 ∷ Bx2-0134 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at021021 c4 = derive (CX31 ∷ Bx2-0134 ∷ CX31 ∷ []) (Bx2-0134 ∷ CCZ034 ∷ [])
  (rw 1 (q260 c4) ∷
   rw 0 (q270 c4) ∷
   rw⁻ 2 (q271 c4) ∷
   rw⁻ 1 (q272 c4) ∷
   rw 4 (q273 c4) ∷
   rw 8 (q274 c4) ∷
   rw 7 (q25 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 5 (q273 c4) ∷
   rw⁻ 3 (q275 c4) ∷
   rw 2 (q270 c4) ∷
   rw 3 (q276 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 3 (q272 c4) ∷
   rw⁻ 0 (q260 c4) ∷
   rw⁻ 1 (q277 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = sE 90 (lem-cQ-at02102331 c4)

-- tP @02102331: 7 steps
lem-tP-at02102331 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at02102331 c4 = derive (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  (rw⁻ 0 (q85 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw 2 (q55 c4) ∷
   rw 1 (q278 c4) ∷
   rw⁻ 2 (q55 c4) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷ []) Eq.refl

private
  q279 : Ws → Eqn
  q279 c4 = wlE 344 (lit c4)
  q280 : Ws → Eqn
  q280 c4 = sE 105 (lem-cQ-at03243042 c4)

-- box-tQ @03243042: 13 steps
lem-box-tQ-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at03243042 c4 = derive (Bx3-1402 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q279 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q279 c4) ∷
   rw 0 (q134 c4) ∷
   rw 2 (q89 c4) ∷
   rw 1 (q280 c4) ∷
   rw 2 (q136 c4) ∷ []) Eq.refl

private
  q281 : Ws → Eqn
  q281 c4 = wpE 661 c4
  q282 : Ws → Eqn
  q282 c4 = wpE 56 c4
  q283 : Ws → Eqn
  q283 c4 = sE 111 (lem-cQ-at142142 c4)
  q284 : Ws → Eqn
  q284 c4 = wpE 57 c4

-- box-tQ @142142: 13 steps
lem-box-tQ-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at142142 c4 = derive (Bx0-4132 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q281 c4) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q281 c4) ∷
   rw 0 (q282 c4) ∷
   rw 2 (q89 c4) ∷
   rw 1 (q283 c4) ∷
   rw 2 (q284 c4) ∷ []) Eq.refl

-- tP @03243042: 7 steps
lem-tP-at03243042 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at03243042 c4 = derive (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q130 c4) ∷
   rw⁻ 3 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q280 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 0 (q131 c4) ∷
   rw 1 (q130 c4) ∷ []) Eq.refl

private
  q285 : Ws → Eqn
  q285 c4 = wpE 1232 c4

-- box-tQ @02102331: 13 steps
lem-box-tQ-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at02102331 c4 = derive (Bx2-0314 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q285 c4) ∷
   re 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q285 c4) ∷
   rw 0 (q250 c4) ∷
   rw 2 (q251 c4) ∷
   rw 1 (q278 c4) ∷
   rw 2 (q252 c4) ∷ []) Eq.refl

-- tP @142142: 7 steps
lem-tP-at142142 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at142142 c4 = derive (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q57 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw 2 (q59 c4) ∷
   rw 1 (q283 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q57 c4) ∷ []) Eq.refl

private
  q286 : Ws → Eqn
  q286 c4 = sE 69 (lem-tP-at032032 c4)

-- t-cP @032032: 5 steps
lem-t-cP-at032032 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-t-cP-at032032 c4 = derive (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q262 c4) ∷
   rw 2 (q263 c4) ∷
   rw 1 (q286 c4) ∷
   rw⁻ 2 (q264 c4) ∷
   rw 3 (q286 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = sE 85 (lem-box-perm-2134-at0210243143 c4)
  q288 : Ws → Eqn
  q288 c4 = wpE 1307 c4

-- S-sym-xt @14213243: 8 steps
lem-S-sym-xt-at14213243 : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ
lem-S-sym-xt-at14213243 c4 = derive (Sb2-0-41-3 ∷ []) (Sb2-4-01-3 ∷ [])
  (re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   rw 0 (q287 c4) ∷
   rw⁻ 1 (q288 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q289 : Ws → Eqn
  q289 c4 = wpE 1309 c4
  q290 : Ws → Eqn
  q290 c4 = sE 108 (lem-cQ-at04122041 c4)
  q291 : Ws → Eqn
  q291 c4 = wpE 1310 c4

-- box-tQ @04122041: 13 steps
lem-box-tQ-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at04122041 c4 = derive (Bx4-2031 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q171 c4) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q171 c4) ∷
   rw 0 (q289 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q290 c4) ∷
   rw 2 (q291 c4) ∷ []) Eq.refl

private
  q292 : Ws → Eqn
  q292 c4 = wlE 453 (lit c4)
  q293 : Ws → Eqn
  q293 c4 = wpE 303 c4
  q294 : Ws → Eqn
  q294 c4 = wlE 454 (lit c4)
  q295 : Ws → Eqn
  q295 c4 = sE 109 (lem-cQ-at0412233041 c4)

-- tP @0412233041: 7 steps
lem-tP-at0412233041 : Ws → ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ
lem-tP-at0412233041 c4 = derive (Toff423 ∷ Toff401 ∷ []) (Toff401 ∷ Toff423 ∷ [])
  (rw⁻ 0 (q292 c4) ∷
   rw⁻ 3 (q293 c4) ∷
   rw 2 (q294 c4) ∷
   rw 1 (q295 c4) ∷
   rw⁻ 2 (q294 c4) ∷
   rw 0 (q293 c4) ∷
   rw 1 (q292 c4) ∷ []) Eq.refl

private
  q296 : Ws → Eqn
  q296 c4 = wpE 1321 c4
  q297 : Ws → Eqn
  q297 c4 = wlE 1472 (lit c4)

-- tP @04122041: 7 steps
lem-tP-at04122041 : Ws → ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ
lem-tP-at04122041 c4 = derive (Toff402 ∷ Toff413 ∷ []) (Toff413 ∷ Toff402 ∷ [])
  (rw⁻ 0 (q296 c4) ∷
   rw⁻ 3 (q297 c4) ∷
   rw 2 (q294 c4) ∷
   rw 1 (q290 c4) ∷
   rw⁻ 2 (q294 c4) ∷
   rw 0 (q297 c4) ∷
   rw 1 (q296 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = sE 79 (lem-box-tQ-at0410213243 c4)
  q299 : Ws → Eqn
  q299 c4 = wpE 368 c4
  q300 : Ws → Eqn
  q300 c4 = wpE 1325 c4
  q301 : Ws → Eqn
  q301 c4 = wlE 1477 (lit c4)

-- CXbc-box @0410213243: 17 steps
lem-CXbc-box-at0410213243 : Ws → ⟪ (CX12 ∷ Bx4-0123 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0410213243 c4 = derive (CX12 ∷ Bx4-0123 ∷ CX12 ∷ []) (Bx4-0123 ∷ CCZ013 ∷ [])
  (rw 1 (q298 c4) ∷
   rw 0 (q299 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 3 (q300 c4) ∷
   rw 2 (q299 c4) ∷
   rw 5 (q199 c4) ∷
   rw⁻ 9 (q200 c4) ∷
   rw 8 (q68 c4) ∷
   rw⁻ 7 (q201 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 5 (q202 c4) ∷
   rw⁻ 6 (q199 c4) ∷
   rw 4 (q45 c4) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 4 (q70 c4) ∷
   rw⁻ 0 (q298 c4) ∷
   rw⁻ 1 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = wpE 1326 c4
  q303 : Ws → Eqn
  q303 c4 = wpE 1327 c4
  q304 : Ws → Eqn
  q304 c4 = wlE 458 (lit c4)
  q305 : Ws → Eqn
  q305 c4 = wpE 1328 c4
  q306 : Ws → Eqn
  q306 c4 = wpE 360 c4
  q307 : Ws → Eqn
  q307 c4 = eqn (CS23⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 (lit c4))
  q308 : Ws → Eqn
  q308 c4 = eqn (CS23 ∷ Toff401 ∷ []) (Toff401 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF401 (lit c4))
  q309 : Ws → Eqn
  q309 c4 = wpE 1329 c4
  q310 : Ws → Eqn
  q310 c4 = wpE 1330 c4
  q311 : Ws → Eqn
  q311 c4 = wpE 550 c4
  q312 : Ws → Eqn
  q312 c4 = wlE 1478 (lit c4)

-- CXcb-box @0410213243: 18 steps
lem-CXcb-box-at0410213243 : Ws → ⟪ (CX21 ∷ Bx4-0123 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at0410213243 c4 = derive (CX21 ∷ Bx4-0123 ∷ CX21 ∷ []) (Bx4-0123 ∷ CCZ023 ∷ [])
  (rw 1 (q298 c4) ∷
   rw 0 (q302 c4) ∷
   rw⁻ 2 (q303 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 4 (q304 c4) ∷
   rw 8 (q305 c4) ∷
   rw 7 (q306 c4) ∷
   rw 6 (q307 c4) ∷
   rw 5 (q306 c4) ∷
   rw 4 (q308 c4) ∷
   rw⁻ 5 (q304 c4) ∷
   rw⁻ 3 (q309 c4) ∷
   rw 2 (q302 c4) ∷
   rw 3 (q310 c4) ∷
   rw 4 (q311 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw⁻ 0 (q298 c4) ∷
   rw⁻ 1 (q312 c4) ∷ []) Eq.refl

private
  q313 : Ws → Eqn
  q313 c4 = wpE 1331 c4
  q314 : Ws → Eqn
  q314 c4 = sE 107 (lem-cQ-at04103143 c4)

-- box-tQ @04103143: 13 steps
lem-box-tQ-at04103143 : Ws → ⟪ (Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at04103143 c4 = derive (Bx4-0213 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q313 c4) ∷
   re 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q313 c4) ∷
   rw 0 (q289 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q314 c4) ∷
   rw 2 (q291 c4) ∷ []) Eq.refl

-- tP @04103143: 7 steps
lem-tP-at04103143 : Ws → ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ
lem-tP-at04103143 c4 = derive (Toff402 ∷ Toff413 ∷ []) (Toff413 ∷ Toff402 ∷ [])
  (rw⁻ 0 (q296 c4) ∷
   rw⁻ 3 (q297 c4) ∷
   rw 2 (q294 c4) ∷
   rw 1 (q314 c4) ∷
   rw⁻ 2 (q294 c4) ∷
   rw 0 (q297 c4) ∷
   rw 1 (q296 c4) ∷ []) Eq.refl

private
  q315 : Ws → Eqn
  q315 c4 = wpE 212 c4
  q316 : Ws → Eqn
  q316 c4 = wlE 1485 (lit c4)
  q317 : Ws → Eqn
  q317 c4 = sE 110 (lem-cQ-at04233042 c4)
  q318 : Ws → Eqn
  q318 c4 = wlE 1486 (lit c4)

-- box-tQ @04233042: 13 steps
lem-box-tQ-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at04233042 c4 = derive (Bx4-1302 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q315 c4) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q315 c4) ∷
   rw 0 (q316 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q317 c4) ∷
   rw 2 (q318 c4) ∷ []) Eq.refl

-- tP @04233042: 7 steps
lem-tP-at04233042 : Ws → ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ
lem-tP-at04233042 c4 = derive (Toff413 ∷ Toff402 ∷ []) (Toff402 ∷ Toff413 ∷ [])
  (rw⁻ 0 (q297 c4) ∷
   rw⁻ 3 (q296 c4) ∷
   rw 2 (q294 c4) ∷
   rw 1 (q317 c4) ∷
   rw⁻ 2 (q294 c4) ∷
   rw 0 (q296 c4) ∷
   rw 1 (q297 c4) ∷ []) Eq.refl
