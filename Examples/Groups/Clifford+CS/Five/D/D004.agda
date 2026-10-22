{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD004 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D004 (Sᴰ : SD004) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX02-CCZ134 ; lem-comm-CX04-CCZ123 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-CCZ013 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CX42-CCZ013 ; lem-comm-SWAP02-BOX⟨4·13⟩ ; lem-comm-SWAP13-BOX⟨0·24⟩ ; lem-comm-SWAP13-BOX⟨0·42⟩ ; lem-comm-SWAP14-BOX⟨0·23⟩ ; lem-comm-SWAP14-BOX⟨0·32⟩ ; lem-comm-SWAP23-BOX⟨0·14⟩ ; lem-comm-SWAP24-BOX⟨0·31⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX03-CCZ124 ; lem-comm-CX30-CCZ124 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-SWAP02-BOX⟨3·14⟩ ; lem-comm-SWAP12-BOX⟨3·04⟩ ; lem-comm-SWAP14-BOX⟨2·03⟩ ; lem-comm-SWAP14-BOX⟨2·30⟩ ; lem-comm-SWAP14-BOX⟨3·20⟩ ; lem-comm-SWAP23-BOX⟨0·41⟩ ; lem-comm-SWAP24-BOX⟨0·13⟩)

-- The lemmas of other derivation modules (DSig).
private
  lem-cQ-at021021 : Ws → St 0
  lem-cQ-at021021 = pickᴰ 0 Sᴰ
  lem-cQ-at0210213443 : Ws → St 1
  lem-cQ-at0210213443 = pickᴰ 1 Sᴰ
  lem-cQ-at03102132 : Ws → St 2
  lem-cQ-at03102132 = pickᴰ 2 Sᴰ
  lem-cQ-at032032 : Ws → St 3
  lem-cQ-at032032 = pickᴰ 3 Sᴰ
  lem-cQ-at0410213243 : Ws → St 4
  lem-cQ-at0410213243 = pickᴰ 4 Sᴰ
  lem-cQ-at04203243 : Ws → St 5
  lem-cQ-at04203243 = pickᴰ 5 Sᴰ
  lem-cQ-at13243142 : Ws → St 6
  lem-cQ-at13243142 = pickᴰ 6 Sᴰ
  lem-cQ-at13243241 : Ws → St 7
  lem-cQ-at13243241 = pickᴰ 7 Sᴰ
  lem-cQ-at14233142 : Ws → St 8
  lem-cQ-at14233142 = pickᴰ 8 Sᴰ
  lem-cQ-at14233241 : Ws → St 9
  lem-cQ-at14233241 = pickᴰ 9 Sᴰ
  lem-sym-ab : Ws → St 10
  lem-sym-ab = pickᴰ 10 Sᴰ
  lem-sym-ab-at03102132 : Ws → St 11
  lem-sym-ab-at03102132 = pickᴰ 11 Sᴰ
  lem-cQ-at0213243140 : Ws → St 12
  lem-cQ-at0213243140 = pickᴰ 12 Sᴰ
  lem-cQ-at0220 : Ws → St 13
  lem-cQ-at0220 = pickᴰ 13 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 155 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 1 c4
  q3 : Ws → Eqn
  q3 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = wpE 2 c4
  q5 : Ws → Eqn
  q5 c4 = wpE 3 c4

-- cQ: 7 steps
lem-cQ : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ c4 = derive (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

private
  q6 : Ws → Eqn
  q6 c4 = wpE 13 c4
  q7 : Ws → Eqn
  q7 c4 = wlE 171 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CX04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = wlE 172 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 173 (lit c4)

-- cQ @0210243143: 7 steps
lem-cQ-at0210243143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at0210243143 c4 = derive (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  (rw 0 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q6 c4) ∷ []) Eq.refl

private
  q11 : Ws → Eqn
  q11 c4 = wpE 46 c4
  q12 : Ws → Eqn
  q12 c4 = wlE 199 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = wpE 47 c4
  q15 : Ws → Eqn
  q15 c4 = wpE 48 c4

-- cQ @243243: 7 steps
lem-cQ-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at243243 c4 = derive (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  (rw 0 (q11 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 1 (q11 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = wpE 75 c4
  q17 : Ws → Eqn
  q17 c4 = wlE 225 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CX24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = wpE 76 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 77 c4

-- cQ @122441: 7 steps
lem-cQ-at122441 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at122441 c4 = derive (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  (rw 0 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 0 (q20 c4) ∷
   rw⁻ 1 (q16 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = wlE 264 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 265 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 266 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 267 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Sw23 ∷ Bx0-14 ∷ []) (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4))
  q26 : Ws → Eqn
  q26 c4 = wlE 3 (lit c4)

-- nat-SWbc: 23 steps
lem-nat-SWbc : Ws → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-nat-SWbc c4 = derive (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (Bx0-1324 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   re 3 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   rw⁻ 2 (q23 c4) ∷
   rw 3 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q24 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 7 (q25 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   re 11 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   rw⁻ 10 (q23 c4) ∷
   rw 11 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 13 (q24 c4) ∷
   rw⁻ 14 (q23 c4) ∷
   rw 15 (q25 c4) ∷
   rw 16 (q26 c4) ∷
   re 2 6 (Bx1-024 ∷ []) ∷
   re 5 6 (Bx1-024 ∷ []) ∷
   re 0 6 (Bx0-1324 ∷ []) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = wlE 269 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 118 c4
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ012 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CZ))
  q30 : Ws → Eqn
  q30 c4 = sE 6 (lem-cQ-at13243142 c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 119 c4

-- box-tQ @13243142: 13 steps
lem-box-tQ-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at13243142 c4 = derive (Bx0-3412 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   re 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = sE 10 (lem-sym-ab c4)

-- box-perm-2134: 1 steps
lem-box-perm-2134 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-box-perm-2134 c4 = derive (Bx0-1234 ∷ []) (Bx0-2134 ∷ [])
  (rw 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = wlE 270 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CX21 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = wpE 120 c4

-- cQ @1221: 7 steps
lem-cQ-at1221 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at1221 c4 = derive (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  (rw 0 (q33 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw 1 (q34 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q33 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wlE 283 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 284 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 285 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 286 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Sw13 ∷ Bx0-24 ∷ []) (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4))
  q41 : Ws → Eqn
  q41 c4 = wlE 287 (lit c4)

-- nat-SWbc @1221: 23 steps
lem-nat-SWbc-at1221 : Ws → ⟪ (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-nat-SWbc-at1221 c4 = derive (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (Bx0-2314 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) ∷
   rw⁻ 0 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   re 3 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q39 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q37 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   re 11 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 10 (q38 c4) ∷
   rw 11 (q39 c4) ∷
   rw 12 (q40 c4) ∷
   rw 13 (q39 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q41 c4) ∷
   re 2 6 (Bx2-014 ∷ []) ∷
   re 5 6 (Bx2-014 ∷ []) ∷
   re 0 6 (Bx0-2314 ∷ []) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = wlE 288 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = sE 7 (lem-cQ-at13243241 c4)

-- box-tQ @13243241: 13 steps
lem-box-tQ-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at13243241 c4 = derive (Bx0-3421 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q42 c4) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q42 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = wlE 289 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 39 c4
  q46 : Ws → Eqn
  q46 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = wpE 32 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 21 c4

-- cQ @2332: 7 steps
lem-cQ-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at2332 c4 = derive (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  (rw 0 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q44 c4) ∷ []) Eq.refl

-- cQ @12243143: 7 steps
lem-cQ-at12243143 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at12243143 c4 = derive (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  (rw 0 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 0 (q20 c4) ∷
   rw⁻ 1 (q16 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wpE 149 c4
  q50 : Ws → Eqn
  q50 c4 = wpE 150 c4
  q51 : Ws → Eqn
  q51 c4 = wpE 151 c4
  q52 : Ws → Eqn
  q52 c4 = wpE 152 c4
  q53 : Ws → Eqn
  q53 c4 = eqn (Sw14 ∷ Bx0-32 ∷ []) (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4))
  q54 : Ws → Eqn
  q54 c4 = wlE 306 (lit c4)

-- nat-SWbc @13243142: 23 steps
lem-nat-SWbc-at13243142 : Ws → ⟪ (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-nat-SWbc-at13243142 c4 = derive (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (Bx0-3142 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   re 3 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   rw⁻ 2 (q51 c4) ∷
   rw 3 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw 5 (q52 c4) ∷
   rw⁻ 6 (q51 c4) ∷
   rw 7 (q53 c4) ∷
   rw 8 (q50 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   re 11 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   rw⁻ 10 (q51 c4) ∷
   rw 11 (q52 c4) ∷
   rw 12 (q53 c4) ∷
   rw 13 (q52 c4) ∷
   rw⁻ 14 (q51 c4) ∷
   rw 15 (q53 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (Bx3-042 ∷ []) ∷
   re 5 6 (Bx3-042 ∷ []) ∷
   re 0 6 (Bx0-3142 ∷ []) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = wlE 307 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 155 c4
  q57 : Ws → Eqn
  q57 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = wpE 156 c4
  q59 : Ws → Eqn
  q59 c4 = wpE 157 c4

-- cQ @122331: 7 steps
lem-cQ-at122331 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at122331 c4 = derive (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  (rw 0 (q55 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q59 c4) ∷
   rw⁻ 1 (q55 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = wpE 175 c4
  q61 : Ws → Eqn
  q61 c4 = wpE 176 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 177 c4
  q63 : Ws → Eqn
  q63 c4 = wpE 178 c4
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw24 ∷ Bx0-31 ∷ []) (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4))
  q65 : Ws → Eqn
  q65 c4 = wlE 322 (lit c4)

-- nat-SWbc @13243241: 23 steps
lem-nat-SWbc-at13243241 : Ws → ⟪ (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-nat-SWbc-at13243241 c4 = derive (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (Bx0-3241 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) ∷
   rw⁻ 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   re 3 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q63 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q61 c4) ∷
   rw⁻ 9 (q60 c4) ∷
   re 11 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   rw⁻ 10 (q62 c4) ∷
   rw 11 (q63 c4) ∷
   rw 12 (q64 c4) ∷
   rw 13 (q63 c4) ∷
   rw⁻ 14 (q62 c4) ∷
   rw 15 (q64 c4) ∷
   rw 16 (q65 c4) ∷
   re 2 6 (Bx3-041 ∷ []) ∷
   re 5 6 (Bx3-041 ∷ []) ∷
   re 0 6 (Bx0-3241 ∷ []) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = wlE 323 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = wpE 179 c4

-- cQ @132132: 7 steps
lem-cQ-at132132 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at132132 c4 = derive (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  (rw 0 (q66 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 0 (q45 c4) ∷
   rw⁻ 1 (q66 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = wpE 194 c4
  q70 : Ws → Eqn
  q70 c4 = wpE 195 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 196 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 197 c4
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw14 ∷ Bx0-23 ∷ []) (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4))

-- nat-SWbc @12243143: 23 steps
lem-nat-SWbc-at12243143 : Ws → ⟪ (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-nat-SWbc-at12243143 c4 = derive (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (Bx0-2143 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) ∷
   rw⁻ 0 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   re 3 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 3 (q72 c4) ∷
   rw 4 (q73 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 7 (q73 c4) ∷
   rw 8 (q70 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   re 11 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   rw⁻ 10 (q71 c4) ∷
   rw 11 (q72 c4) ∷
   rw 12 (q73 c4) ∷
   rw 13 (q72 c4) ∷
   rw⁻ 14 (q71 c4) ∷
   rw 15 (q73 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (Bx2-043 ∷ []) ∷
   re 5 6 (Bx2-043 ∷ []) ∷
   re 0 6 (Bx0-2143 ∷ []) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = wpE 136 c4
  q75 : Ws → Eqn
  q75 c4 = sE 8 (lem-cQ-at14233142 c4)

-- box-tQ @14233142: 13 steps
lem-box-tQ-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at14233142 c4 = derive (Bx0-4312 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q74 c4) ∷
   re 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q74 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = wpE 206 c4
  q77 : Ws → Eqn
  q77 c4 = wpE 207 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 208 c4
  q79 : Ws → Eqn
  q79 c4 = wpE 209 c4
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw13 ∷ Bx0-42 ∷ []) (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4))

-- nat-SWbc @14233142: 23 steps
lem-nat-SWbc-at14233142 : Ws → ⟪ (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-nat-SWbc-at14233142 c4 = derive (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (Bx0-4132 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) ∷
   rw⁻ 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   re 3 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   rw⁻ 2 (q78 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q80 c4) ∷
   rw 5 (q79 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 7 (q80 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   re 11 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   rw⁻ 10 (q78 c4) ∷
   rw 11 (q79 c4) ∷
   rw 12 (q80 c4) ∷
   rw 13 (q79 c4) ∷
   rw⁻ 14 (q78 c4) ∷
   rw 15 (q80 c4) ∷
   rw 16 (q41 c4) ∷
   re 2 6 (Bx4-032 ∷ []) ∷
   re 5 6 (Bx4-032 ∷ []) ∷
   re 0 6 (Bx0-4132 ∷ []) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wpE 4 c4
  q82 : Ws → Eqn
  q82 c4 = wlE 156 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 157 (lit c4)

-- tP @14233142: 7 steps
lem-tP-at14233142 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at14233142 c4 = derive (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q75 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q81 c4) ∷ []) Eq.refl

-- cQ @3443: 7 steps
lem-cQ-at3443 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at3443 c4 = derive (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  (rw 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

-- cQ @13213442: 7 steps
lem-cQ-at13213442 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at13213442 c4 = derive (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  (rw 0 (q66 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 0 (q45 c4) ∷
   rw⁻ 1 (q66 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = wpE 213 c4
  q85 : Ws → Eqn
  q85 c4 = eqn (CX42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = wlE 342 (lit c4)

-- cQ @1441: 7 steps
lem-cQ-at1441 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at1441 c4 = derive (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  (rw 0 (q84 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q85 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 1 (q85 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q84 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = wlE 343 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CX32 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = wpE 215 c4

-- cQ @1331: 7 steps
lem-cQ-at1331 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at1331 c4 = derive (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  (rw 0 (q87 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 1 (q87 c4) ∷ []) Eq.refl

-- cQ @2442: 7 steps
lem-cQ-at2442 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at2442 c4 = derive (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  (rw 0 (q11 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 1 (q11 c4) ∷ []) Eq.refl

-- cQ @12233441: 7 steps
lem-cQ-at12233441 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at12233441 c4 = derive (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  (rw 0 (q55 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q59 c4) ∷
   rw⁻ 1 (q55 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = wlE 391 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wpE 261 c4
  q92 : Ws → Eqn
  q92 c4 = eqn (CX02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = wlE 392 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wlE 393 (lit c4)

-- cQ @0110: 7 steps
lem-cQ-at0110 : Ws → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0110 c4 = derive (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  (rw 0 (q90 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw 3 (q92 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 1 (q92 c4) ∷
   rw⁻ 0 (q94 c4) ∷
   rw⁻ 1 (q90 c4) ∷ []) Eq.refl

-- cQ @133441: 7 steps
lem-cQ-at133441 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at133441 c4 = derive (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  (rw 0 (q87 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 1 (q87 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = wpE 273 c4
  q96 : Ws → Eqn
  q96 c4 = wpE 274 c4

-- nat-SWbc @133441: 23 steps
lem-nat-SWbc-at133441 : Ws → ⟪ (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-nat-SWbc-at133441 c4 = derive (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (Bx0-3421 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q95 c4) ∷
   re 3 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   rw⁻ 2 (q60 c4) ∷
   rw 3 (q96 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q96 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q95 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   re 11 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   rw⁻ 10 (q60 c4) ∷
   rw 11 (q96 c4) ∷
   rw 12 (q64 c4) ∷
   rw 13 (q96 c4) ∷
   rw⁻ 14 (q60 c4) ∷
   rw 15 (q64 c4) ∷
   rw 16 (q65 c4) ∷
   re 2 6 (Bx3-021 ∷ []) ∷
   re 5 6 (Bx3-021 ∷ []) ∷
   re 0 6 (Bx0-3421 ∷ []) ∷ []) Eq.refl

-- tP @13243241: 7 steps
lem-tP-at13243241 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at13243241 c4 = derive (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q43 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q81 c4) ∷ []) Eq.refl

-- cQ @233442: 7 steps
lem-cQ-at233442 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at233442 c4 = derive (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  (rw 0 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q44 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = wlE 416 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = wlE 417 (lit c4)
  q99 : Ws → Eqn
  q99 c4 = wlE 175 (lit c4)
  q100 : Ws → Eqn
  q100 c4 = sE 0 (lem-cQ-at021021 c4)

-- tP @021021: 7 steps
lem-tP-at021021 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at021021 c4 = derive (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw⁻ 3 (q98 c4) ∷
   rw 2 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q97 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = wpE 288 c4
  q102 : Ws → Eqn
  q102 c4 = wpE 289 c4

-- nat-SWbc @13213442: 23 steps
lem-nat-SWbc-at13213442 : Ws → ⟪ (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-nat-SWbc-at13213442 c4 = derive (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (Bx0-3412 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) ∷
   rw⁻ 0 (q51 c4) ∷
   rw 1 (q101 c4) ∷
   re 3 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 3 (q102 c4) ∷
   rw 4 (q53 c4) ∷
   rw 5 (q102 c4) ∷
   rw⁻ 6 (q49 c4) ∷
   rw 7 (q53 c4) ∷
   rw 8 (q101 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   re 11 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   rw⁻ 10 (q49 c4) ∷
   rw 11 (q102 c4) ∷
   rw 12 (q53 c4) ∷
   rw 13 (q102 c4) ∷
   rw⁻ 14 (q49 c4) ∷
   rw 15 (q53 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (Bx3-012 ∷ []) ∷
   re 5 6 (Bx3-012 ∷ []) ∷
   re 0 6 (Bx0-3412 ∷ []) ∷ []) Eq.refl

-- tP @13243142: 7 steps
lem-tP-at13243142 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at13243142 c4 = derive (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q30 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q81 c4) ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = wlE 434 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 435 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 436 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = sE 2 (lem-cQ-at03102132 c4)

-- tP @03102132: 7 steps
lem-tP-at03102132 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at03102132 c4 = derive (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q103 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q103 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = wpE 303 c4
  q108 : Ws → Eqn
  q108 c4 = wlE 453 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 454 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = sE 4 (lem-cQ-at0410213243 c4)

-- tP @0410213243: 7 steps
lem-tP-at0410213243 : Ws → ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-tP-at0410213243 c4 = derive (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ [])
  (rw⁻ 0 (q107 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 2 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   rw 0 (q108 c4) ∷
   rw 1 (q107 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = wlE 256 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = wpE 106 c4
  q113 : Ws → Eqn
  q113 c4 = wpE 107 c4
  q114 : Ws → Eqn
  q114 c4 = wpE 108 c4

-- cQ @043043: 7 steps
lem-cQ-at043043 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at043043 c4 = derive (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  (rw 0 (q111 c4) ∷
   rw⁻ 4 (q112 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q114 c4) ∷
   rw⁻ 1 (q111 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = wlE 207 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = wpE 312 c4
  q117 : Ws → Eqn
  q117 c4 = wpE 313 c4
  q118 : Ws → Eqn
  q118 c4 = wpE 314 c4

-- cQ @0330: 7 steps
lem-cQ-at0330 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0330 c4 = derive (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  (rw 0 (q115 c4) ∷
   rw⁻ 4 (q116 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 2 (q117 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q118 c4) ∷
   rw⁻ 1 (q115 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = wpE 337 c4
  q120 : Ws → Eqn
  q120 c4 = wpE 338 c4
  q121 : Ws → Eqn
  q121 c4 = wpE 339 c4
  q122 : Ws → Eqn
  q122 c4 = wpE 340 c4
  q123 : Ws → Eqn
  q123 c4 = eqn (Sw02 ∷ Bx4-13 ∷ []) (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4))
  q124 : Ws → Eqn
  q124 c4 = wlE 485 (lit c4)

-- nat-SWbc @043043: 23 steps
lem-nat-SWbc-at043043 : Ws → ⟪ (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-nat-SWbc-at043043 c4 = derive (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (Bx4-1023 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   re 3 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) ∷
   rw⁻ 2 (q121 c4) ∷
   rw 3 (q122 c4) ∷
   rw 4 (q123 c4) ∷
   rw 5 (q122 c4) ∷
   rw⁻ 6 (q121 c4) ∷
   rw 7 (q123 c4) ∷
   rw 8 (q120 c4) ∷
   rw⁻ 9 (q119 c4) ∷
   re 11 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) ∷
   rw⁻ 10 (q121 c4) ∷
   rw 11 (q122 c4) ∷
   rw 12 (q123 c4) ∷
   rw 13 (q122 c4) ∷
   rw⁻ 14 (q121 c4) ∷
   rw 15 (q123 c4) ∷
   rw 16 (q124 c4) ∷
   re 2 6 (Bx1-423 ∷ []) ∷
   re 5 6 (Bx1-423 ∷ []) ∷
   re 0 6 (Bx4-1023 ∷ []) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = sE 5 (lem-cQ-at04203243 c4)

-- tP @04203243: 7 steps
lem-tP-at04203243 : Ws → ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-tP-at04203243 c4 = derive (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ [])
  (rw⁻ 0 (q107 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 2 (q109 c4) ∷
   rw 1 (q125 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   rw 0 (q108 c4) ∷
   rw 1 (q107 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = wpE 352 c4
  q127 : Ws → Eqn
  q127 c4 = wlE 490 (lit c4)
  q128 : Ws → Eqn
  q128 c4 = wlE 491 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 492 (lit c4)

-- cQ @0310243142: 7 steps
lem-cQ-at0310243142 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0310243142 c4 = derive (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  (rw 0 (q126 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 0 (q129 c4) ∷
   rw⁻ 1 (q126 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = wpE 305 c4
  q131 : Ws → Eqn
  q131 c4 = wpE 355 c4
  q132 : Ws → Eqn
  q132 c4 = eqn (CZ01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ))
  q133 : Ws → Eqn
  q133 c4 = wpE 356 c4

-- box-tQ @0410213243: 13 steps
lem-box-tQ-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0410213243 c4 = derive (Bx4-0123 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q130 c4) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q130 c4) ∷
   rw 0 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q133 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = wpE 320 c4
  q135 : Ws → Eqn
  q135 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = wlE 495 (lit c4)

-- cQ @0314203142: 7 steps
lem-cQ-at0314203142 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0314203142 c4 = derive (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  (rw 0 (q134 c4) ∷
   rw⁻ 4 (q129 c4) ∷
   rw 3 (q135 c4) ∷
   rw⁻ 2 (q136 c4) ∷
   rw 1 (q135 c4) ∷
   rw⁻ 0 (q127 c4) ∷
   rw⁻ 1 (q134 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = wlE 486 (lit c4)

-- box-tQ @04203243: 13 steps
lem-box-tQ-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at04203243 c4 = derive (Bx4-1023 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw 2 (q137 c4) ∷
   re 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw 5 (q137 c4) ∷
   rw 0 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q133 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = wpE 370 c4
  q139 : Ws → Eqn
  q139 c4 = wpE 371 c4

-- nat-SWbc @04203243: 23 steps
lem-nat-SWbc-at04203243 : Ws → ⟪ (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-nat-SWbc-at04203243 c4 = derive (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (Bx4-1203 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 1 (q138 c4) ∷
   re 3 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 3 (q139 c4) ∷
   rw 4 (q123 c4) ∷
   rw 5 (q139 c4) ∷
   rw⁻ 6 (q119 c4) ∷
   rw 7 (q123 c4) ∷
   rw 8 (q138 c4) ∷
   rw⁻ 9 (q121 c4) ∷
   re 11 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   rw⁻ 10 (q119 c4) ∷
   rw 11 (q139 c4) ∷
   rw 12 (q123 c4) ∷
   rw 13 (q139 c4) ∷
   rw⁻ 14 (q119 c4) ∷
   rw 15 (q123 c4) ∷
   rw 16 (q124 c4) ∷
   re 2 6 (Bx1-403 ∷ []) ∷
   re 5 6 (Bx1-403 ∷ []) ∷
   re 0 6 (Bx4-1203 ∷ []) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = wlE 518 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 519 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = sE 3 (lem-cQ-at032032 c4)
  q143 : Ws → Eqn
  q143 c4 = wlE 520 (lit c4)

-- box-tQ @032032: 13 steps
lem-box-tQ-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at032032 c4 = derive (Bx3-1024 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q140 c4) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q140 c4) ∷
   rw 0 (q141 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = wlE 528 (lit c4)
  q145 : Ws → Eqn
  q145 c4 = wlE 529 (lit c4)
  q146 : Ws → Eqn
  q146 c4 = wlE 530 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = wlE 531 (lit c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (Sw02 ∷ Bx3-14 ∷ []) (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4))

-- nat-SWbc @032032: 23 steps
lem-nat-SWbc-at032032 : Ws → ⟪ (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-nat-SWbc-at032032 c4 = derive (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (Bx3-1204 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) ∷
   rw⁻ 0 (q144 c4) ∷
   rw 1 (q145 c4) ∷
   re 3 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   rw⁻ 2 (q146 c4) ∷
   rw 3 (q147 c4) ∷
   rw 4 (q148 c4) ∷
   rw 5 (q147 c4) ∷
   rw⁻ 6 (q146 c4) ∷
   rw 7 (q148 c4) ∷
   rw 8 (q145 c4) ∷
   rw⁻ 9 (q144 c4) ∷
   re 11 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   rw⁻ 10 (q146 c4) ∷
   rw 11 (q147 c4) ∷
   rw 12 (q148 c4) ∷
   rw 13 (q147 c4) ∷
   rw⁻ 14 (q146 c4) ∷
   rw 15 (q148 c4) ∷
   rw 16 (q124 c4) ∷
   re 2 6 (Bx1-304 ∷ []) ∷
   re 5 6 (Bx1-304 ∷ []) ∷
   re 0 6 (Bx3-1204 ∷ []) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = wlE 539 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 540 (lit c4)

-- nat-SWbc @0330: 23 steps
lem-nat-SWbc-at0330 : Ws → ⟪ (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-nat-SWbc-at0330 c4 = derive (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (Bx3-1024 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) ∷
   rw⁻ 0 (q146 c4) ∷
   rw 1 (q149 c4) ∷
   re 3 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   rw⁻ 2 (q144 c4) ∷
   rw 3 (q150 c4) ∷
   rw 4 (q148 c4) ∷
   rw 5 (q150 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw 7 (q148 c4) ∷
   rw 8 (q149 c4) ∷
   rw⁻ 9 (q146 c4) ∷
   re 11 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   rw⁻ 10 (q144 c4) ∷
   rw 11 (q150 c4) ∷
   rw 12 (q148 c4) ∷
   rw 13 (q150 c4) ∷
   rw⁻ 14 (q144 c4) ∷
   rw 15 (q148 c4) ∷
   rw 16 (q124 c4) ∷
   re 2 6 (Bx1-324 ∷ []) ∷
   re 5 6 (Bx1-324 ∷ []) ∷
   re 0 6 (Bx3-1024 ∷ []) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = wpE 496 c4
  q152 : Ws → Eqn
  q152 c4 = wlE 611 (lit c4)

-- cQ @0214203143: 7 steps
lem-cQ-at0214203143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at0214203143 c4 = derive (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  (rw 0 (q151 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 3 (q135 c4) ∷
   rw⁻ 2 (q152 c4) ∷
   rw 1 (q135 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q151 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = wlE 334 (lit c4)
  q154 : Ws → Eqn
  q154 c4 = wpE 513 c4
  q155 : Ws → Eqn
  q155 c4 = eqn (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = wlE 620 (lit c4)
  q157 : Ws → Eqn
  q157 c4 = wlE 621 (lit c4)

-- cQ @0214213043: 7 steps
lem-cQ-at0214213043 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0214213043 c4 = derive (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  (rw 0 (q153 c4) ∷
   rw⁻ 4 (q154 c4) ∷
   rw 3 (q155 c4) ∷
   rw⁻ 2 (q156 c4) ∷
   rw 1 (q155 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw⁻ 1 (q153 c4) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = wlE 637 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wpE 515 c4
  q160 : Ws → Eqn
  q160 c4 = eqn (CX03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = wlE 638 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = wlE 639 (lit c4)

-- cQ @0210233441: 7 steps
lem-cQ-at0210233441 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0210233441 c4 = derive (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  (rw 0 (q158 c4) ∷
   rw⁻ 4 (q159 c4) ∷
   rw 3 (q160 c4) ∷
   rw⁻ 2 (q161 c4) ∷
   rw 1 (q160 c4) ∷
   rw⁻ 0 (q162 c4) ∷
   rw⁻ 1 (q158 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = wpE 540 c4
  q164 : Ws → Eqn
  q164 c4 = wlE 667 (lit c4)

-- cQ @14213243: 7 steps
lem-cQ-at14213243 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at14213243 c4 = derive (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  (rw 0 (q163 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 3 (q155 c4) ∷
   rw⁻ 2 (q164 c4) ∷
   rw 1 (q155 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw⁻ 1 (q163 c4) ∷ []) Eq.refl

-- cQ @143143: 7 steps
lem-cQ-at143143 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at143143 c4 = derive (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  (rw 0 (q84 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 3 (q85 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 1 (q85 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q84 c4) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = wpE 569 c4
  q166 : Ws → Eqn
  q166 c4 = wpE 570 c4
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw14 ∷ Bx2-03 ∷ []) (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4))

-- nat-SWbc @0210243143: 23 steps
lem-nat-SWbc-at0210243143 : Ws → ⟪ (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210243143 c4 = derive (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (Bx2-0143 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw⁻ 0 (q69 c4) ∷
   rw 1 (q165 c4) ∷
   re 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q167 c4) ∷
   rw 5 (q166 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 7 (q167 c4) ∷
   rw 8 (q165 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   re 11 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   rw⁻ 10 (q71 c4) ∷
   rw 11 (q166 c4) ∷
   rw 12 (q167 c4) ∷
   rw 13 (q166 c4) ∷
   rw⁻ 14 (q71 c4) ∷
   rw 15 (q167 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (Bx0-243 ∷ []) ∷
   re 5 6 (Bx0-243 ∷ []) ∷
   re 0 6 (Bx2-0143 ∷ []) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = sE 1 (lem-cQ-at0210213443 c4)

-- tP @0210213443: 7 steps
lem-tP-at0210213443 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at0210213443 c4 = derive (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw⁻ 3 (q98 c4) ∷
   rw 2 (q99 c4) ∷
   rw 1 (q168 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q97 c4) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = wpE 582 c4
  q170 : Ws → Eqn
  q170 c4 = wpE 583 c4
  q171 : Ws → Eqn
  q171 c4 = wpE 584 c4
  q172 : Ws → Eqn
  q172 c4 = wpE 585 c4
  q173 : Ws → Eqn
  q173 c4 = eqn (Sw24 ∷ Bx0-13 ∷ []) (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4))

-- nat-SWbc @243243: 23 steps
lem-nat-SWbc-at243243 : Ws → ⟪ (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-nat-SWbc-at243243 c4 = derive (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (Bx0-1243 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   rw⁻ 0 (q169 c4) ∷
   rw 1 (q170 c4) ∷
   re 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 3 (q172 c4) ∷
   rw 4 (q173 c4) ∷
   rw 5 (q172 c4) ∷
   rw⁻ 6 (q171 c4) ∷
   rw 7 (q173 c4) ∷
   rw 8 (q170 c4) ∷
   rw⁻ 9 (q169 c4) ∷
   re 11 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   rw⁻ 10 (q171 c4) ∷
   rw 11 (q172 c4) ∷
   rw 12 (q173 c4) ∷
   rw 13 (q172 c4) ∷
   rw⁻ 14 (q171 c4) ∷
   rw 15 (q173 c4) ∷
   rw 16 (q65 c4) ∷
   re 2 6 (Bx1-043 ∷ []) ∷
   re 5 6 (Bx1-043 ∷ []) ∷
   re 0 6 (Bx0-1243 ∷ []) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = wpE 594 c4
  q175 : Ws → Eqn
  q175 c4 = wpE 595 c4
  q176 : Ws → Eqn
  q176 c4 = wpE 596 c4
  q177 : Ws → Eqn
  q177 c4 = wpE 597 c4
  q178 : Ws → Eqn
  q178 c4 = eqn (Sw23 ∷ Bx0-41 ∷ []) (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4))

-- nat-SWbc @1441: 23 steps
lem-nat-SWbc-at1441 : Ws → ⟪ (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-nat-SWbc-at1441 c4 = derive (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (Bx0-4321 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) ∷
   rw⁻ 0 (q174 c4) ∷
   rw 1 (q175 c4) ∷
   re 3 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   rw⁻ 2 (q176 c4) ∷
   rw 3 (q177 c4) ∷
   rw 4 (q178 c4) ∷
   rw 5 (q177 c4) ∷
   rw⁻ 6 (q176 c4) ∷
   rw 7 (q178 c4) ∷
   rw 8 (q175 c4) ∷
   rw⁻ 9 (q174 c4) ∷
   re 11 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   rw⁻ 10 (q176 c4) ∷
   rw 11 (q177 c4) ∷
   rw 12 (q178 c4) ∷
   rw 13 (q177 c4) ∷
   rw⁻ 14 (q176 c4) ∷
   rw 15 (q178 c4) ∷
   rw 16 (q26 c4) ∷
   re 2 6 (Bx4-021 ∷ []) ∷
   re 5 6 (Bx4-021 ∷ []) ∷
   re 0 6 (Bx0-4321 ∷ []) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = wpE 162 c4
  q180 : Ws → Eqn
  q180 c4 = sE 9 (lem-cQ-at14233241 c4)

-- box-tQ @14233241: 13 steps
lem-box-tQ-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at14233241 c4 = derive (Bx0-4321 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q179 c4) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q179 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q180 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

-- tP @14233241: 7 steps
lem-tP-at14233241 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at14233241 c4 = derive (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  (rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q180 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q81 c4) ∷ []) Eq.refl

-- cQ @12213443: 7 steps
lem-cQ-at12213443 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at12213443 c4 = derive (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  (rw 0 (q33 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw 1 (q34 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q33 c4) ∷ []) Eq.refl

private
  q181 : Ws → Eqn
  q181 c4 = wlE 617 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = wpE 543 c4
  q183 : Ws → Eqn
  q183 c4 = wlE 669 (lit c4)
  q184 : Ws → Eqn
  q184 c4 = wlE 670 (lit c4)

-- cQ @0314213042: 7 steps
lem-cQ-at0314213042 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0314213042 c4 = derive (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  (rw 0 (q181 c4) ∷
   rw⁻ 4 (q182 c4) ∷
   rw 3 (q155 c4) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 1 (q155 c4) ∷
   rw⁻ 0 (q184 c4) ∷
   rw⁻ 1 (q181 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = wlE 757 (lit c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CX30 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = wpE 679 c4

-- cQ @0213203441: 7 steps
lem-cQ-at0213203441 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0213203441 c4 = derive (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  (rw 0 (q185 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   rw 3 (q186 c4) ∷
   rw⁻ 2 (q187 c4) ∷
   rw 1 (q186 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q185 c4) ∷ []) Eq.refl

-- tP @032032: 7 steps
lem-tP-at032032 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at032032 c4 = derive (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q103 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 1 (q142 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q103 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = wlE 245 (lit c4)
  q189 : Ws → Eqn
  q189 c4 = wlE 324 (lit c4)
  q190 : Ws → Eqn
  q190 c4 = wpE 184 c4
  q191 : Ws → Eqn
  q191 c4 = wpE 185 c4

-- cQ @0312243140: 7 steps
lem-cQ-at0312243140 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0312243140 c4 = derive (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  (rw 0 (q188 c4) ∷
   rw⁻ 4 (q189 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 2 (q190 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 0 (q191 c4) ∷
   rw⁻ 1 (q188 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = wlE 854 (lit c4)
  q193 : Ws → Eqn
  q193 c4 = wlE 855 (lit c4)
  q194 : Ws → Eqn
  q194 c4 = wlE 856 (lit c4)
  q195 : Ws → Eqn
  q195 c4 = wlE 857 (lit c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (Sw14 ∷ Bx3-20 ∷ []) (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4))

-- nat-SWbc @0312243140: 23 steps
lem-nat-SWbc-at0312243140 : Ws → ⟪ (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312243140 c4 = derive (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (Bx3-2140 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) ∷
   rw⁻ 0 (q192 c4) ∷
   rw 1 (q193 c4) ∷
   re 3 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) ∷
   rw⁻ 2 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw 4 (q196 c4) ∷
   rw 5 (q195 c4) ∷
   rw⁻ 6 (q194 c4) ∷
   rw 7 (q196 c4) ∷
   rw 8 (q193 c4) ∷
   rw⁻ 9 (q192 c4) ∷
   re 11 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) ∷
   rw⁻ 10 (q194 c4) ∷
   rw 11 (q195 c4) ∷
   rw 12 (q196 c4) ∷
   rw 13 (q195 c4) ∷
   rw⁻ 14 (q194 c4) ∷
   rw 15 (q196 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (Bx2-340 ∷ []) ∷
   re 5 6 (Bx2-340 ∷ []) ∷
   re 0 6 (Bx3-2140 ∷ []) ∷ []) Eq.refl

-- cQ @033440: 7 steps
lem-cQ-at033440 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at033440 c4 = derive (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  (rw 0 (q115 c4) ∷
   rw⁻ 4 (q116 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 2 (q117 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q118 c4) ∷
   rw⁻ 1 (q115 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = wlE 326 (lit c4)
  q198 : Ws → Eqn
  q198 c4 = wpE 734 c4

-- cQ @0312213440: 7 steps
lem-cQ-at0312213440 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0312213440 c4 = derive (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  (rw 0 (q197 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 2 (q198 c4) ∷
   rw 1 (q34 c4) ∷
   rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q197 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = wlE 864 (lit c4)
  q200 : Ws → Eqn
  q200 c4 = wlE 865 (lit c4)

-- nat-SWbc @0312213440: 23 steps
lem-nat-SWbc-at0312213440 : Ws → ⟪ (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312213440 c4 = derive (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (Bx3-2410 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q199 c4) ∷
   re 3 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) ∷
   rw⁻ 2 (q192 c4) ∷
   rw 3 (q200 c4) ∷
   rw 4 (q196 c4) ∷
   rw 5 (q200 c4) ∷
   rw⁻ 6 (q192 c4) ∷
   rw 7 (q196 c4) ∷
   rw 8 (q199 c4) ∷
   rw⁻ 9 (q194 c4) ∷
   re 11 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) ∷
   rw⁻ 10 (q192 c4) ∷
   rw 11 (q200 c4) ∷
   rw 12 (q196 c4) ∷
   rw 13 (q200 c4) ∷
   rw⁻ 14 (q192 c4) ∷
   rw 15 (q196 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (Bx2-310 ∷ []) ∷
   re 5 6 (Bx2-310 ∷ []) ∷
   re 0 6 (Bx3-2410 ∷ []) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = wlE 242 (lit c4)
  q202 : Ws → Eqn
  q202 c4 = wpE 81 c4
  q203 : Ws → Eqn
  q203 c4 = wpE 91 c4
  q204 : Ws → Eqn
  q204 c4 = wpE 92 c4

-- cQ @022330: 7 steps
lem-cQ-at022330 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at022330 c4 = derive (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  (rw 0 (q201 c4) ∷
   rw⁻ 4 (q202 c4) ∷
   rw 3 (q46 c4) ∷
   rw⁻ 2 (q203 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 0 (q204 c4) ∷
   rw⁻ 1 (q201 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = wlE 930 (lit c4)
  q206 : Ws → Eqn
  q206 c4 = sE 13 (lem-cQ-at0220 c4)
  q207 : Ws → Eqn
  q207 c4 = wlE 931 (lit c4)

-- box-tQ @0220: 13 steps
lem-box-tQ-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0220 c4 = derive (Bx2-1034 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q140 c4) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q140 c4) ∷
   rw 0 (q205 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q206 c4) ∷
   rw 2 (q207 c4) ∷ []) Eq.refl

-- tP @0220: 7 steps
lem-tP-at0220 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at0220 c4 = derive (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q97 c4) ∷
   rw⁻ 3 (q98 c4) ∷
   rw 2 (q99 c4) ∷
   rw 1 (q206 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q97 c4) ∷ []) Eq.refl

private
  q208 : Ws → Eqn
  q208 c4 = wlE 935 (lit c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 936 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = sE 12 (lem-cQ-at0213243140 c4)
  q211 : Ws → Eqn
  q211 c4 = wlE 937 (lit c4)

-- box-tQ @0213243140: 13 steps
lem-box-tQ-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0213243140 c4 = derive (Bx2-3410 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q208 c4) ∷
   re 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q208 c4) ∷
   rw 0 (q209 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q210 c4) ∷
   rw 2 (q211 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = eqn (Sw14 ∷ Bx2-30 ∷ []) (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4))

-- nat-SWbc @0213243140: 23 steps
lem-nat-SWbc-at0213243140 : Ws → ⟪ (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-nat-SWbc-at0213243140 c4 = derive (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (Bx2-3140 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) ∷
   rw⁻ 0 (q192 c4) ∷
   rw 1 (q200 c4) ∷
   re 3 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   rw⁻ 2 (q194 c4) ∷
   rw 3 (q199 c4) ∷
   rw 4 (q212 c4) ∷
   rw 5 (q199 c4) ∷
   rw⁻ 6 (q194 c4) ∷
   rw 7 (q212 c4) ∷
   rw 8 (q200 c4) ∷
   rw⁻ 9 (q192 c4) ∷
   re 11 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   rw⁻ 10 (q194 c4) ∷
   rw 11 (q199 c4) ∷
   rw 12 (q212 c4) ∷
   rw 13 (q199 c4) ∷
   rw⁻ 14 (q194 c4) ∷
   rw 15 (q212 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (Bx3-240 ∷ []) ∷
   re 5 6 (Bx3-240 ∷ []) ∷
   re 0 6 (Bx2-3140 ∷ []) ∷ []) Eq.refl

-- cQ @02233440: 7 steps
lem-cQ-at02233440 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at02233440 c4 = derive (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  (rw 0 (q201 c4) ∷
   rw⁻ 4 (q202 c4) ∷
   rw 3 (q46 c4) ∷
   rw⁻ 2 (q203 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 0 (q204 c4) ∷
   rw⁻ 1 (q201 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = wlE 297 (lit c4)
  q214 : Ws → Eqn
  q214 c4 = wpE 87 c4

-- cQ @0213213440: 7 steps
lem-cQ-at0213213440 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0213213440 c4 = derive (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  (rw 0 (q213 c4) ∷
   rw⁻ 4 (q204 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 2 (q214 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 0 (q202 c4) ∷
   rw⁻ 1 (q213 c4) ∷ []) Eq.refl

-- nat-SWbc @0213213440: 23 steps
lem-nat-SWbc-at0213213440 : Ws → ⟪ (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-nat-SWbc-at0213213440 c4 = derive (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (Bx2-3410 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q195 c4) ∷
   re 3 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   rw⁻ 2 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q212 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 6 (q192 c4) ∷
   rw 7 (q212 c4) ∷
   rw 8 (q195 c4) ∷
   rw⁻ 9 (q194 c4) ∷
   re 11 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   rw⁻ 10 (q192 c4) ∷
   rw 11 (q193 c4) ∷
   rw 12 (q212 c4) ∷
   rw 13 (q193 c4) ∷
   rw⁻ 14 (q192 c4) ∷
   rw 15 (q212 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (Bx3-210 ∷ []) ∷
   re 5 6 (Bx3-210 ∷ []) ∷
   re 0 6 (Bx2-3410 ∷ []) ∷ []) Eq.refl

-- tP @0213243140: 7 steps
lem-tP-at0213243140 : Ws → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0213243140 c4 = derive (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  (rw⁻ 0 (q98 c4) ∷
   rw⁻ 3 (q97 c4) ∷
   rw 2 (q99 c4) ∷
   rw 1 (q210 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 0 (q97 c4) ∷
   rw 1 (q98 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = wlE 989 (lit c4)
  q216 : Ws → Eqn
  q216 c4 = wlE 990 (lit c4)

-- nat-SWbc @122331: 23 steps
lem-nat-SWbc-at122331 : Ws → ⟪ (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-nat-SWbc-at122331 c4 = derive (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (Bx0-2134 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) ∷
   rw⁻ 0 (q38 c4) ∷
   rw 1 (q215 c4) ∷
   re 3 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q216 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q216 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q215 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   re 11 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 10 (q36 c4) ∷
   rw 11 (q216 c4) ∷
   rw 12 (q40 c4) ∷
   rw 13 (q216 c4) ∷
   rw⁻ 14 (q36 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q41 c4) ∷
   re 2 6 (Bx2-034 ∷ []) ∷
   re 5 6 (Bx2-034 ∷ []) ∷
   re 0 6 (Bx0-2134 ∷ []) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = wlE 1023 (lit c4)
  q218 : Ws → Eqn
  q218 c4 = wlE 1024 (lit c4)

-- nat-SWbc @2332: 23 steps
lem-nat-SWbc-at2332 : Ws → ⟪ (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-nat-SWbc-at2332 c4 = derive (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (Bx0-1234 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) ∷
   rw⁻ 0 (q23 c4) ∷
   rw 1 (q217 c4) ∷
   re 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q218 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q218 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 7 (q25 c4) ∷
   rw 8 (q217 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   re 11 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   rw⁻ 10 (q21 c4) ∷
   rw 11 (q218 c4) ∷
   rw 12 (q25 c4) ∷
   rw 13 (q218 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw 15 (q25 c4) ∷
   rw 16 (q26 c4) ∷
   re 2 6 (Bx1-034 ∷ []) ∷
   re 5 6 (Bx1-034 ∷ []) ∷
   re 0 6 (Bx0-1234 ∷ []) ∷ []) Eq.refl

-- box-tQ @0210213443: 13 steps
lem-box-tQ-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q130 c4) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q130 c4) ∷
   rw 0 (q205 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q168 c4) ∷
   rw 2 (q207 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = sE 11 (lem-sym-ab-at03102132 c4)

-- box-perm-2134 @03102132: 1 steps
lem-box-perm-2134-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2134-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-1024 ∷ [])
  (rw 0 (q219 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = wpE 280 c4

-- box-tQ @03102132: 13 steps
lem-box-tQ-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at03102132 c4 = derive (Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q220 c4) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q220 c4) ∷
   rw 0 (q141 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q143 c4) ∷ []) Eq.refl

private
  q221 : Ws → Eqn
  q221 c4 = wlE 840 (lit c4)
  q222 : Ws → Eqn
  q222 c4 = wlE 841 (lit c4)
  q223 : Ws → Eqn
  q223 c4 = wlE 838 (lit c4)
  q224 : Ws → Eqn
  q224 c4 = wlE 839 (lit c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (Sw12 ∷ Bx3-04 ∷ []) (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4))
  q226 : Ws → Eqn
  q226 c4 = wlE 6 (lit c4)

-- nat-SWbc @03102132: 23 steps
lem-nat-SWbc-at03102132 : Ws → ⟪ (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-nat-SWbc-at03102132 c4 = derive (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (Bx3-0214 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   re 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   rw⁻ 2 (q223 c4) ∷
   rw 3 (q224 c4) ∷
   rw 4 (q225 c4) ∷
   rw 5 (q224 c4) ∷
   rw⁻ 6 (q223 c4) ∷
   rw 7 (q225 c4) ∷
   rw 8 (q222 c4) ∷
   rw⁻ 9 (q221 c4) ∷
   re 11 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   rw⁻ 10 (q223 c4) ∷
   rw 11 (q224 c4) ∷
   rw 12 (q225 c4) ∷
   rw 13 (q224 c4) ∷
   rw⁻ 14 (q223 c4) ∷
   rw 15 (q225 c4) ∷
   rw 16 (q226 c4) ∷
   re 2 6 (Bx0-314 ∷ []) ∷
   re 5 6 (Bx0-314 ∷ []) ∷
   re 0 6 (Bx3-0214 ∷ []) ∷ []) Eq.refl

private
  q227 : Ws → Eqn
  q227 c4 = wlE 220 (lit c4)
  q228 : Ws → Eqn
  q228 c4 = wpE 820 c4

-- cQ @022440: 7 steps
lem-cQ-at022440 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at022440 c4 = derive (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  (rw 0 (q227 c4) ∷
   rw⁻ 4 (q157 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 2 (q228 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 0 (q154 c4) ∷
   rw⁻ 1 (q227 c4) ∷ []) Eq.refl

-- cQ @02102441: 7 steps
lem-cQ-at02102441 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at02102441 c4 = derive (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  (rw 0 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q6 c4) ∷ []) Eq.refl
