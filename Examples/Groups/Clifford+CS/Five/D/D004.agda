{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD004 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D004 (Sᴰ : SD004) where

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
  lem-comm-CX02-CCZ134 : Ws → St 0
  lem-comm-CX02-CCZ134 = pickᴰ 0 Sᴰ
  lem-comm-CX04-CCZ123 : Ws → St 1
  lem-comm-CX04-CCZ123 = pickᴰ 1 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 2 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 3 Sᴰ
  lem-comm-CX14-CCZ023 : Ws → St 4
  lem-comm-CX14-CCZ023 = pickᴰ 4 Sᴰ
  lem-comm-CX21-CCZ034 : Ws → St 5
  lem-comm-CX21-CCZ034 = pickᴰ 5 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 6 Sᴰ
  lem-comm-CX24-CCZ013 : Ws → St 7
  lem-comm-CX24-CCZ013 = pickᴰ 7 Sᴰ
  lem-comm-CX31-CCZ024 : Ws → St 8
  lem-comm-CX31-CCZ024 = pickᴰ 8 Sᴰ
  lem-comm-CX32-CCZ014 : Ws → St 9
  lem-comm-CX32-CCZ014 = pickᴰ 9 Sᴰ
  lem-comm-CX42-CCZ013 : Ws → St 10
  lem-comm-CX42-CCZ013 = pickᴰ 10 Sᴰ
  lem-comm-SWAP02-BOX⟨4·13⟩ : Ws → St 11
  lem-comm-SWAP02-BOX⟨4·13⟩ = pickᴰ 11 Sᴰ
  lem-comm-SWAP13-BOX⟨0·24⟩ : Ws → St 12
  lem-comm-SWAP13-BOX⟨0·24⟩ = pickᴰ 12 Sᴰ
  lem-comm-SWAP13-BOX⟨0·42⟩ : Ws → St 13
  lem-comm-SWAP13-BOX⟨0·42⟩ = pickᴰ 13 Sᴰ
  lem-comm-SWAP14-BOX⟨0·23⟩ : Ws → St 14
  lem-comm-SWAP14-BOX⟨0·23⟩ = pickᴰ 14 Sᴰ
  lem-comm-SWAP14-BOX⟨0·32⟩ : Ws → St 15
  lem-comm-SWAP14-BOX⟨0·32⟩ = pickᴰ 15 Sᴰ
  lem-comm-SWAP23-BOX⟨0·14⟩ : Ws → St 16
  lem-comm-SWAP23-BOX⟨0·14⟩ = pickᴰ 16 Sᴰ
  lem-comm-SWAP24-BOX⟨0·31⟩ : Ws → St 17
  lem-comm-SWAP24-BOX⟨0·31⟩ = pickᴰ 17 Sᴰ
  lem-comm-CX03-CCZ124 : Ws → St 18
  lem-comm-CX03-CCZ124 = pickᴰ 18 Sᴰ
  lem-comm-CX30-CCZ124 : Ws → St 19
  lem-comm-CX30-CCZ124 = pickᴰ 19 Sᴰ
  lem-comm-CX40-CCZ123 : Ws → St 20
  lem-comm-CX40-CCZ123 = pickᴰ 20 Sᴰ
  lem-comm-CX41-CCZ023 : Ws → St 21
  lem-comm-CX41-CCZ023 = pickᴰ 21 Sᴰ
  lem-comm-SWAP02-BOX⟨3·14⟩ : Ws → St 22
  lem-comm-SWAP02-BOX⟨3·14⟩ = pickᴰ 22 Sᴰ
  lem-comm-SWAP12-BOX⟨3·04⟩ : Ws → St 23
  lem-comm-SWAP12-BOX⟨3·04⟩ = pickᴰ 23 Sᴰ
  lem-comm-SWAP14-BOX⟨2·03⟩ : Ws → St 24
  lem-comm-SWAP14-BOX⟨2·03⟩ = pickᴰ 24 Sᴰ
  lem-comm-SWAP14-BOX⟨2·30⟩ : Ws → St 25
  lem-comm-SWAP14-BOX⟨2·30⟩ = pickᴰ 25 Sᴰ
  lem-comm-SWAP14-BOX⟨3·20⟩ : Ws → St 26
  lem-comm-SWAP14-BOX⟨3·20⟩ = pickᴰ 26 Sᴰ
  lem-comm-SWAP23-BOX⟨0·41⟩ : Ws → St 27
  lem-comm-SWAP23-BOX⟨0·41⟩ = pickᴰ 27 Sᴰ
  lem-comm-SWAP24-BOX⟨0·13⟩ : Ws → St 28
  lem-comm-SWAP24-BOX⟨0·13⟩ = pickᴰ 28 Sᴰ
  lem-cQ-at021021 : Ws → St 29
  lem-cQ-at021021 = pickᴰ 29 Sᴰ
  lem-cQ-at0210213443 : Ws → St 30
  lem-cQ-at0210213443 = pickᴰ 30 Sᴰ
  lem-cQ-at03102132 : Ws → St 31
  lem-cQ-at03102132 = pickᴰ 31 Sᴰ
  lem-cQ-at032032 : Ws → St 32
  lem-cQ-at032032 = pickᴰ 32 Sᴰ
  lem-cQ-at0410213243 : Ws → St 33
  lem-cQ-at0410213243 = pickᴰ 33 Sᴰ
  lem-cQ-at04203243 : Ws → St 34
  lem-cQ-at04203243 = pickᴰ 34 Sᴰ
  lem-cQ-at13243142 : Ws → St 35
  lem-cQ-at13243142 = pickᴰ 35 Sᴰ
  lem-cQ-at13243241 : Ws → St 36
  lem-cQ-at13243241 = pickᴰ 36 Sᴰ
  lem-cQ-at14233142 : Ws → St 37
  lem-cQ-at14233142 = pickᴰ 37 Sᴰ
  lem-cQ-at14233241 : Ws → St 38
  lem-cQ-at14233241 = pickᴰ 38 Sᴰ
  lem-sym-ab : Ws → St 39
  lem-sym-ab = pickᴰ 39 Sᴰ
  lem-sym-ab-at03102132 : Ws → St 40
  lem-sym-ab-at03102132 = pickᴰ 40 Sᴰ
  lem-cQ-at0213243140 : Ws → St 41
  lem-cQ-at0213243140 = pickᴰ 41 Sᴰ
  lem-cQ-at0220 : Ws → St 42
  lem-cQ-at0220 = pickᴰ 42 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 155 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 1 c4
  q3 : Ws → Eqn
  q3 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q4 : Ws → Eqn
  q4 c4 = wpE 2 c4
  q5 : Ws → Eqn
  q5 c4 = wpE 3 c4

-- cQ: 7 steps
lem-cQ : Ws → ⟪ (ℓ "二亠") ⟫ʷ ≈ ⟪ (ℓ "亠二") ⟫ʷ
lem-cQ c4 = derive (ℓ "二亠") (ℓ "亠二")
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
  q8 c4 = sE 1 (lem-comm-CX04-CCZ123 c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 172 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 173 (lit c4)

-- cQ @0210243143: 7 steps
lem-cQ-at0210243143 : Ws → ⟪ (ℓ "亜交") ⟫ʷ ≈ ⟪ (ℓ "交亜") ⟫ʷ
lem-cQ-at0210243143 c4 = derive (ℓ "亜交") (ℓ "交亜")
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
  q13 c4 = sE 4 (lem-comm-CX14-CCZ023 c4)
  q14 : Ws → Eqn
  q14 c4 = wpE 47 c4
  q15 : Ws → Eqn
  q15 c4 = wpE 48 c4

-- cQ @243243: 7 steps
lem-cQ-at243243 : Ws → ⟪ (ℓ "五亘") ⟫ʷ ≈ ⟪ (ℓ "亘五") ⟫ʷ
lem-cQ-at243243 c4 = derive (ℓ "五亘") (ℓ "亘五")
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
  q18 c4 = sE 7 (lem-comm-CX24-CCZ013 c4)
  q19 : Ws → Eqn
  q19 c4 = wpE 76 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 77 c4

-- cQ @122441: 7 steps
lem-cQ-at122441 : Ws → ⟪ (ℓ "亜亐") ⟫ʷ ≈ ⟪ (ℓ "亐亜") ⟫ʷ
lem-cQ-at122441 c4 = derive (ℓ "亜亐") (ℓ "亐亜")
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
  q25 c4 = sE 16 (lem-comm-SWAP23-BOX⟨0·14⟩ c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 3 (lit c4)

-- nat-SWbc: 23 steps
lem-nat-SWbc : Ws → ⟪ (ℓ "乥亹乥") ⟫ʷ ≈ ⟪ (ℓ "亾") ⟫ʷ
lem-nat-SWbc c4 = derive (ℓ "乥亹乥") (ℓ "亾")
  (re 1 1 (ℓ "二亍亸亍二亸") ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   re 3 1 (ℓ "亐互亷互亐亷") ∷
   rw⁻ 2 (q23 c4) ∷
   rw 3 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q24 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 7 (q25 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   re 11 1 (ℓ "亐互亷互亐亷") ∷
   rw⁻ 10 (q23 c4) ∷
   rw 11 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 13 (q24 c4) ∷
   rw⁻ 14 (q23 c4) ∷
   rw 15 (q25 c4) ∷
   rw 16 (q26 c4) ∷
   re 2 6 (ℓ "亽") ∷
   re 5 6 (ℓ "亽") ∷
   re 0 6 (ℓ "亾") ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = wlE 269 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 118 c4
  q29 : Ws → Eqn
  q29 c4 = eqn (ℓ "二乻") (ℓ "乻二") (c₃ (CCZ) (CZ))
  q30 : Ws → Eqn
  q30 c4 = sE 35 (lem-cQ-at13243142 c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 119 c4

-- box-tQ @13243142: 13 steps
lem-box-tQ-at13243142 : Ws → ⟪ (ℓ "仳") ⟫ʷ ≈ ⟪ (ℓ "亡二亡二") ⟫ʷ
lem-box-tQ-at13243142 c4 = derive (ℓ "仳") (ℓ "亡二亡二")
  (re 0 1 (ℓ "亠亡仲亡亠仲") ∷
   re 2 1 (ℓ "亐亓仧亓亐仧") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q27 c4) ∷
   re 5 1 (ℓ "亐亓仧亓亐仧") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q27 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = sE 39 (lem-sym-ab c4)

-- box-perm-2134: 1 steps
lem-box-perm-2134 : Ws → ⟪ (ℓ "亹") ⟫ʷ ≈ ⟪ (ℓ "仌") ⟫ʷ
lem-box-perm-2134 c4 = derive (ℓ "亹") (ℓ "仌")
  (rw 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = wlE 270 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = sE 5 (lem-comm-CX21-CCZ034 c4)
  q35 : Ws → Eqn
  q35 c4 = wpE 120 c4

-- cQ @1221: 7 steps
lem-cQ-at1221 : Ws → ⟪ (ℓ "二亠") ⟫ʷ ≈ ⟪ (ℓ "亠二") ⟫ʷ
lem-cQ-at1221 c4 = derive (ℓ "二亠") (ℓ "亠二")
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
  q40 c4 = sE 12 (lem-comm-SWAP13-BOX⟨0·24⟩ c4)
  q41 : Ws → Eqn
  q41 c4 = wlE 287 (lit c4)

-- nat-SWbc @1221: 23 steps
lem-nat-SWbc-at1221 : Ws → ⟪ (ℓ "乑仌乑") ⟫ʷ ≈ ⟪ (ℓ "仕") ⟫ʷ
lem-nat-SWbc-at1221 c4 = derive (ℓ "乑仌乑") (ℓ "仕")
  (re 1 1 (ℓ "二亍介亍二介") ∷
   rw⁻ 0 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   re 3 1 (ℓ "亘亚今亚亘今") ∷
   rw⁻ 2 (q38 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q39 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q37 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   re 11 1 (ℓ "亘亚今亚亘今") ∷
   rw⁻ 10 (q38 c4) ∷
   rw 11 (q39 c4) ∷
   rw 12 (q40 c4) ∷
   rw 13 (q39 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q41 c4) ∷
   re 2 6 (ℓ "仔") ∷
   re 5 6 (ℓ "仔") ∷
   re 0 6 (ℓ "仕") ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = wlE 288 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = sE 36 (lem-cQ-at13243241 c4)

-- box-tQ @13243241: 13 steps
lem-box-tQ-at13243241 : Ws → ⟪ (ℓ "件") ⟫ʷ ≈ ⟪ (ℓ "亡二亡二") ⟫ʷ
lem-box-tQ-at13243241 c4 = derive (ℓ "件") (ℓ "亡二亡二")
  (re 0 1 (ℓ "亠亡仵亡亠仵") ∷
   re 2 1 (ℓ "亘些仟些亘仟") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q42 c4) ∷
   re 5 1 (ℓ "亘些仟些亘仟") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
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
  q46 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 32 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 21 c4

-- cQ @2332: 7 steps
lem-cQ-at2332 : Ws → ⟪ (ℓ "亐亜") ⟫ʷ ≈ ⟪ (ℓ "亜亐") ⟫ʷ
lem-cQ-at2332 c4 = derive (ℓ "亐亜") (ℓ "亜亐")
  (rw 0 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw⁻ 2 (q47 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q44 c4) ∷ []) Eq.refl

-- cQ @12243143: 7 steps
lem-cQ-at12243143 : Ws → ⟪ (ℓ "亜亐") ⟫ʷ ≈ ⟪ (ℓ "亐亜") ⟫ʷ
lem-cQ-at12243143 c4 = derive (ℓ "亜亐") (ℓ "亐亜")
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
  q53 c4 = sE 15 (lem-comm-SWAP14-BOX⟨0·32⟩ c4)
  q54 : Ws → Eqn
  q54 c4 = wlE 306 (lit c4)

-- nat-SWbc @13243142: 23 steps
lem-nat-SWbc-at13243142 : Ws → ⟪ (ℓ "乘仳乘") ⟫ʷ ≈ ⟪ (ℓ "仩") ⟫ʷ
lem-nat-SWbc-at13243142 c4 = derive (ℓ "乘仳乘") (ℓ "仩")
  (re 1 1 (ℓ "亠亡仲亡亠仲") ∷
   rw⁻ 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   re 3 1 (ℓ "亐亓仧亓亐仧") ∷
   rw⁻ 2 (q51 c4) ∷
   rw 3 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw 5 (q52 c4) ∷
   rw⁻ 6 (q51 c4) ∷
   rw 7 (q53 c4) ∷
   rw 8 (q50 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   re 11 1 (ℓ "亐亓仧亓亐仧") ∷
   rw⁻ 10 (q51 c4) ∷
   rw 11 (q52 c4) ∷
   rw 12 (q53 c4) ∷
   rw 13 (q52 c4) ∷
   rw⁻ 14 (q51 c4) ∷
   rw 15 (q53 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (ℓ "仨") ∷
   re 5 6 (ℓ "仨") ∷
   re 0 6 (ℓ "仩") ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = wlE 307 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 155 c4
  q57 : Ws → Eqn
  q57 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q58 : Ws → Eqn
  q58 c4 = wpE 156 c4
  q59 : Ws → Eqn
  q59 c4 = wpE 157 c4

-- cQ @122331: 7 steps
lem-cQ-at122331 : Ws → ⟪ (ℓ "亘五") ⟫ʷ ≈ ⟪ (ℓ "五亘") ⟫ʷ
lem-cQ-at122331 c4 = derive (ℓ "亘五") (ℓ "五亘")
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
  q64 c4 = sE 17 (lem-comm-SWAP24-BOX⟨0·31⟩ c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 322 (lit c4)

-- nat-SWbc @13243241: 23 steps
lem-nat-SWbc-at13243241 : Ws → ⟪ (ℓ "乬件乬") ⟫ʷ ≈ ⟪ (ℓ "仰") ⟫ʷ
lem-nat-SWbc-at13243241 c4 = derive (ℓ "乬件乬") (ℓ "仰")
  (re 1 1 (ℓ "亠亡仵亡亠仵") ∷
   rw⁻ 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   re 3 1 (ℓ "亘些仟些亘仟") ∷
   rw⁻ 2 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q63 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q61 c4) ∷
   rw⁻ 9 (q60 c4) ∷
   re 11 1 (ℓ "亘些仟些亘仟") ∷
   rw⁻ 10 (q62 c4) ∷
   rw 11 (q63 c4) ∷
   rw 12 (q64 c4) ∷
   rw 13 (q63 c4) ∷
   rw⁻ 14 (q62 c4) ∷
   rw 15 (q64 c4) ∷
   rw 16 (q65 c4) ∷
   re 2 6 (ℓ "仯") ∷
   re 5 6 (ℓ "仯") ∷
   re 0 6 (ℓ "仰") ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = wlE 323 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = sE 8 (lem-comm-CX31-CCZ024 c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 179 c4

-- cQ @132132: 7 steps
lem-cQ-at132132 : Ws → ⟪ (ℓ "亐亜") ⟫ʷ ≈ ⟪ (ℓ "亜亐") ⟫ʷ
lem-cQ-at132132 c4 = derive (ℓ "亐亜") (ℓ "亜亐")
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
  q73 c4 = sE 14 (lem-comm-SWAP14-BOX⟨0·23⟩ c4)

-- nat-SWbc @12243143: 23 steps
lem-nat-SWbc-at12243143 : Ws → ⟪ (ℓ "乘仛乘") ⟫ʷ ≈ ⟪ (ℓ "仑") ⟫ʷ
lem-nat-SWbc-at12243143 c4 = derive (ℓ "乘仛乘") (ℓ "仑")
  (re 1 1 (ℓ "亜亝仚亝亜仚") ∷
   rw⁻ 0 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   re 3 1 (ℓ "二亏仏亏二仏") ∷
   rw⁻ 2 (q71 c4) ∷
   rw 3 (q72 c4) ∷
   rw 4 (q73 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 7 (q73 c4) ∷
   rw 8 (q70 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   re 11 1 (ℓ "二亏仏亏二仏") ∷
   rw⁻ 10 (q71 c4) ∷
   rw 11 (q72 c4) ∷
   rw 12 (q73 c4) ∷
   rw 13 (q72 c4) ∷
   rw⁻ 14 (q71 c4) ∷
   rw 15 (q73 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (ℓ "仐") ∷
   re 5 6 (ℓ "仐") ∷
   re 0 6 (ℓ "仑") ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = wpE 136 c4
  q75 : Ws → Eqn
  q75 c4 = sE 37 (lem-cQ-at14233142 c4)

-- box-tQ @14233142: 13 steps
lem-box-tQ-at14233142 : Ws → ⟪ (ℓ "伋") ⟫ʷ ≈ ⟪ (ℓ "亡二亡二") ⟫ʷ
lem-box-tQ-at14233142 c4 = derive (ℓ "伋") (ℓ "亡二亡二")
  (re 0 1 (ℓ "亠亡伊亡亠伊") ∷
   re 2 1 (ℓ "五亗仿亗五仿") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw⁻ 2 (q74 c4) ∷
   re 5 1 (ℓ "五亗仿亗五仿") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
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
  q80 c4 = sE 13 (lem-comm-SWAP13-BOX⟨0·42⟩ c4)

-- nat-SWbc @14233142: 23 steps
lem-nat-SWbc-at14233142 : Ws → ⟪ (ℓ "乑伋乑") ⟫ʷ ≈ ⟪ (ℓ "企") ⟫ʷ
lem-nat-SWbc-at14233142 c4 = derive (ℓ "乑伋乑") (ℓ "企")
  (re 1 1 (ℓ "亠亡伊亡亠伊") ∷
   rw⁻ 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   re 3 1 (ℓ "五亗仿亗五仿") ∷
   rw⁻ 2 (q78 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q80 c4) ∷
   rw 5 (q79 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 7 (q80 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   re 11 1 (ℓ "五亗仿亗五仿") ∷
   rw⁻ 10 (q78 c4) ∷
   rw 11 (q79 c4) ∷
   rw 12 (q80 c4) ∷
   rw 13 (q79 c4) ∷
   rw⁻ 14 (q78 c4) ∷
   rw 15 (q80 c4) ∷
   rw 16 (q41 c4) ∷
   re 2 6 (ℓ "伀") ∷
   re 5 6 (ℓ "伀") ∷
   re 0 6 (ℓ "企") ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wpE 4 c4
  q82 : Ws → Eqn
  q82 c4 = wlE 156 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 157 (lit c4)

-- tP @14233142: 7 steps
lem-tP-at14233142 : Ws → ⟪ (ℓ "亡亍") ⟫ʷ ≈ ⟪ (ℓ "亍亡") ⟫ʷ
lem-tP-at14233142 c4 = derive (ℓ "亡亍") (ℓ "亍亡")
  (rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q75 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q81 c4) ∷ []) Eq.refl

-- cQ @3443: 7 steps
lem-cQ-at3443 : Ws → ⟪ (ℓ "二亠") ⟫ʷ ≈ ⟪ (ℓ "亠二") ⟫ʷ
lem-cQ-at3443 c4 = derive (ℓ "二亠") (ℓ "亠二")
  (rw 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw⁻ 1 (q1 c4) ∷ []) Eq.refl

-- cQ @13213442: 7 steps
lem-cQ-at13213442 : Ws → ⟪ (ℓ "亐亜") ⟫ʷ ≈ ⟪ (ℓ "亜亐") ⟫ʷ
lem-cQ-at13213442 c4 = derive (ℓ "亐亜") (ℓ "亜亐")
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
  q85 c4 = sE 10 (lem-comm-CX42-CCZ013 c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 342 (lit c4)

-- cQ @1441: 7 steps
lem-cQ-at1441 : Ws → ⟪ (ℓ "亜亐") ⟫ʷ ≈ ⟪ (ℓ "亐亜") ⟫ʷ
lem-cQ-at1441 c4 = derive (ℓ "亜亐") (ℓ "亐亜")
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
  q88 c4 = sE 9 (lem-comm-CX32-CCZ014 c4)
  q89 : Ws → Eqn
  q89 c4 = wpE 215 c4

-- cQ @1331: 7 steps
lem-cQ-at1331 : Ws → ⟪ (ℓ "亘五") ⟫ʷ ≈ ⟪ (ℓ "五亘") ⟫ʷ
lem-cQ-at1331 c4 = derive (ℓ "亘五") (ℓ "五亘")
  (rw 0 (q87 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 1 (q87 c4) ∷ []) Eq.refl

-- cQ @2442: 7 steps
lem-cQ-at2442 : Ws → ⟪ (ℓ "五亘") ⟫ʷ ≈ ⟪ (ℓ "亘五") ⟫ʷ
lem-cQ-at2442 c4 = derive (ℓ "五亘") (ℓ "亘五")
  (rw 0 (q11 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 1 (q11 c4) ∷ []) Eq.refl

-- cQ @12233441: 7 steps
lem-cQ-at12233441 : Ws → ⟪ (ℓ "亘五") ⟫ʷ ≈ ⟪ (ℓ "五亘") ⟫ʷ
lem-cQ-at12233441 c4 = derive (ℓ "亘五") (ℓ "五亘")
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
  q92 c4 = sE 0 (lem-comm-CX02-CCZ134 c4)
  q93 : Ws → Eqn
  q93 c4 = wlE 392 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wlE 393 (lit c4)

-- cQ @0110: 7 steps
lem-cQ-at0110 : Ws → ⟪ (ℓ "二京") ⟫ʷ ≈ ⟪ (ℓ "京二") ⟫ʷ
lem-cQ-at0110 c4 = derive (ℓ "二京") (ℓ "京二")
  (rw 0 (q90 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw 3 (q92 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 1 (q92 c4) ∷
   rw⁻ 0 (q94 c4) ∷
   rw⁻ 1 (q90 c4) ∷ []) Eq.refl

-- cQ @133441: 7 steps
lem-cQ-at133441 : Ws → ⟪ (ℓ "亘五") ⟫ʷ ≈ ⟪ (ℓ "五亘") ⟫ʷ
lem-cQ-at133441 c4 = derive (ℓ "亘五") (ℓ "五亘")
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
lem-nat-SWbc-at133441 : Ws → ⟪ (ℓ "乬仰乬") ⟫ʷ ≈ ⟪ (ℓ "件") ⟫ʷ
lem-nat-SWbc-at133441 c4 = derive (ℓ "乬仰乬") (ℓ "件")
  (re 1 1 (ℓ "亘亙仯亙亘仯") ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q95 c4) ∷
   re 3 1 (ℓ "亠亢仟亢亠仟") ∷
   rw⁻ 2 (q60 c4) ∷
   rw 3 (q96 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q96 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q95 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   re 11 1 (ℓ "亠亢仟亢亠仟") ∷
   rw⁻ 10 (q60 c4) ∷
   rw 11 (q96 c4) ∷
   rw 12 (q64 c4) ∷
   rw 13 (q96 c4) ∷
   rw⁻ 14 (q60 c4) ∷
   rw 15 (q64 c4) ∷
   rw 16 (q65 c4) ∷
   re 2 6 (ℓ "仵") ∷
   re 5 6 (ℓ "仵") ∷
   re 0 6 (ℓ "件") ∷ []) Eq.refl

-- tP @13243241: 7 steps
lem-tP-at13243241 : Ws → ⟪ (ℓ "亡亍") ⟫ʷ ≈ ⟪ (ℓ "亍亡") ⟫ʷ
lem-tP-at13243241 c4 = derive (ℓ "亡亍") (ℓ "亍亡")
  (rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q43 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q81 c4) ∷ []) Eq.refl

-- cQ @233442: 7 steps
lem-cQ-at233442 : Ws → ⟪ (ℓ "亐亜") ⟫ʷ ≈ ⟪ (ℓ "亜亐") ⟫ʷ
lem-cQ-at233442 c4 = derive (ℓ "亐亜") (ℓ "亜亐")
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
  q100 c4 = sE 29 (lem-cQ-at021021 c4)

-- tP @021021: 7 steps
lem-tP-at021021 : Ws → ⟪ (ℓ "亏亱") ⟫ʷ ≈ ⟪ (ℓ "亱亏") ⟫ʷ
lem-tP-at021021 c4 = derive (ℓ "亏亱") (ℓ "亱亏")
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
lem-nat-SWbc-at13213442 : Ws → ⟪ (ℓ "乘仩乘") ⟫ʷ ≈ ⟪ (ℓ "仳") ⟫ʷ
lem-nat-SWbc-at13213442 c4 = derive (ℓ "乘仩乘") (ℓ "仳")
  (re 1 1 (ℓ "亐云仨云亐仨") ∷
   rw⁻ 0 (q51 c4) ∷
   rw 1 (q101 c4) ∷
   re 3 1 (ℓ "亠亢仧亢亠仧") ∷
   rw⁻ 2 (q49 c4) ∷
   rw 3 (q102 c4) ∷
   rw 4 (q53 c4) ∷
   rw 5 (q102 c4) ∷
   rw⁻ 6 (q49 c4) ∷
   rw 7 (q53 c4) ∷
   rw 8 (q101 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   re 11 1 (ℓ "亠亢仧亢亠仧") ∷
   rw⁻ 10 (q49 c4) ∷
   rw 11 (q102 c4) ∷
   rw 12 (q53 c4) ∷
   rw 13 (q102 c4) ∷
   rw⁻ 14 (q49 c4) ∷
   rw 15 (q53 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (ℓ "仲") ∷
   re 5 6 (ℓ "仲") ∷
   re 0 6 (ℓ "仳") ∷ []) Eq.refl

-- tP @13243142: 7 steps
lem-tP-at13243142 : Ws → ⟪ (ℓ "亡亍") ⟫ʷ ≈ ⟪ (ℓ "亍亡") ⟫ʷ
lem-tP-at13243142 c4 = derive (ℓ "亡亍") (ℓ "亍亡")
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
  q106 c4 = sE 31 (lem-cQ-at03102132 c4)

-- tP @03102132: 7 steps
lem-tP-at03102132 : Ws → ⟪ (ℓ "亓亲") ⟫ʷ ≈ ⟪ (ℓ "亲亓") ⟫ʷ
lem-tP-at03102132 c4 = derive (ℓ "亓亲") (ℓ "亲亓")
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
  q110 c4 = sE 33 (lem-cQ-at0410213243 c4)

-- tP @0410213243: 7 steps
lem-tP-at0410213243 : Ws → ⟪ (ℓ "亗亳") ⟫ʷ ≈ ⟪ (ℓ "亳亗") ⟫ʷ
lem-tP-at0410213243 c4 = derive (ℓ "亗亳") (ℓ "亳亗")
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
lem-cQ-at043043 : Ws → ⟪ (ℓ "亨亠") ⟫ʷ ≈ ⟪ (ℓ "亠亨") ⟫ʷ
lem-cQ-at043043 c4 = derive (ℓ "亨亠") (ℓ "亠亨")
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
lem-cQ-at0330 : Ws → ⟪ (ℓ "交亠") ⟫ʷ ≈ ⟪ (ℓ "亠交") ⟫ʷ
lem-cQ-at0330 c4 = derive (ℓ "交亠") (ℓ "亠交")
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
  q123 c4 = sE 11 (lem-comm-SWAP02-BOX⟨4·13⟩ c4)
  q124 : Ws → Eqn
  q124 c4 = wlE 485 (lit c4)

-- nat-SWbc @043043: 23 steps
lem-nat-SWbc-at043043 : Ws → ⟪ (ℓ "串侓串") ⟫ʷ ≈ ⟪ (ℓ "侒") ⟫ʷ
lem-nat-SWbc-at043043 c4 = derive (ℓ "串侓串") (ℓ "侒")
  (re 1 1 (ℓ "亨享伥享亨伥") ∷
   rw⁻ 0 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   re 3 1 (ℓ "五亖伤亖五伤") ∷
   rw⁻ 2 (q121 c4) ∷
   rw 3 (q122 c4) ∷
   rw 4 (q123 c4) ∷
   rw 5 (q122 c4) ∷
   rw⁻ 6 (q121 c4) ∷
   rw 7 (q123 c4) ∷
   rw 8 (q120 c4) ∷
   rw⁻ 9 (q119 c4) ∷
   re 11 1 (ℓ "五亖伤亖五伤") ∷
   rw⁻ 10 (q121 c4) ∷
   rw 11 (q122 c4) ∷
   rw 12 (q123 c4) ∷
   rw 13 (q122 c4) ∷
   rw⁻ 14 (q121 c4) ∷
   rw 15 (q123 c4) ∷
   rw 16 (q124 c4) ∷
   re 2 6 (ℓ "伫") ∷
   re 5 6 (ℓ "伫") ∷
   re 0 6 (ℓ "侒") ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = sE 34 (lem-cQ-at04203243 c4)

-- tP @04203243: 7 steps
lem-tP-at04203243 : Ws → ⟪ (ℓ "亗亳") ⟫ʷ ≈ ⟪ (ℓ "亳亗") ⟫ʷ
lem-tP-at04203243 c4 = derive (ℓ "亗亳") (ℓ "亳亗")
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
lem-cQ-at0310243142 : Ws → ⟪ (ℓ "亠交") ⟫ʷ ≈ ⟪ (ℓ "交亠") ⟫ʷ
lem-cQ-at0310243142 c4 = derive (ℓ "亠交") (ℓ "交亠")
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
  q132 c4 = eqn (ℓ "个亰") (ℓ "亰个") (c₂ (CZ) (CCZ))
  q133 : Ws → Eqn
  q133 c4 = wpE 356 c4

-- box-tQ @0410213243: 13 steps
lem-box-tQ-at0410213243 : Ws → ⟪ (ℓ "侍") ⟫ʷ ≈ ⟪ (ℓ "亗亰亗亰") ⟫ʷ
lem-box-tQ-at0410213243 c4 = derive (ℓ "侍") (ℓ "亗亰亗亰")
  (re 0 1 (ℓ "五亗伆亗五伆") ∷
   re 2 1 (ℓ "亜亝份亝亜份") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw 2 (q130 c4) ∷
   re 5 1 (ℓ "亜亝份亝亜份") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw 5 (q130 c4) ∷
   rw 0 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q133 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = wpE 320 c4
  q135 : Ws → Eqn
  q135 c4 = sE 20 (lem-comm-CX40-CCZ123 c4)
  q136 : Ws → Eqn
  q136 c4 = wlE 495 (lit c4)

-- cQ @0314203142: 7 steps
lem-cQ-at0314203142 : Ws → ⟪ (ℓ "亠交") ⟫ʷ ≈ ⟪ (ℓ "交亠") ⟫ʷ
lem-cQ-at0314203142 c4 = derive (ℓ "亠交") (ℓ "交亠")
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
lem-box-tQ-at04203243 : Ws → ⟪ (ℓ "侒") ⟫ʷ ≈ ⟪ (ℓ "亗亰亗亰") ⟫ʷ
lem-box-tQ-at04203243 c4 = derive (ℓ "侒") (ℓ "亗亰亗亰")
  (re 0 1 (ℓ "五亗伫亗五伫") ∷
   re 2 1 (ℓ "亨亩伤亩亨伤") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw 2 (q137 c4) ∷
   re 5 1 (ℓ "亨亩伤亩亨伤") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
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
lem-nat-SWbc-at04203243 : Ws → ⟪ (ℓ "串侒串") ⟫ʷ ≈ ⟪ (ℓ "侓") ⟫ʷ
lem-nat-SWbc-at04203243 c4 = derive (ℓ "串侒串") (ℓ "侓")
  (re 1 1 (ℓ "五亗伫亗五伫") ∷
   rw⁻ 0 (q121 c4) ∷
   rw 1 (q138 c4) ∷
   re 3 1 (ℓ "亨亩伤亩亨伤") ∷
   rw⁻ 2 (q119 c4) ∷
   rw 3 (q139 c4) ∷
   rw 4 (q123 c4) ∷
   rw 5 (q139 c4) ∷
   rw⁻ 6 (q119 c4) ∷
   rw 7 (q123 c4) ∷
   rw 8 (q138 c4) ∷
   rw⁻ 9 (q121 c4) ∷
   re 11 1 (ℓ "亨亩伤亩亨伤") ∷
   rw⁻ 10 (q119 c4) ∷
   rw 11 (q139 c4) ∷
   rw 12 (q123 c4) ∷
   rw 13 (q139 c4) ∷
   rw⁻ 14 (q119 c4) ∷
   rw 15 (q123 c4) ∷
   rw 16 (q124 c4) ∷
   re 2 6 (ℓ "伥") ∷
   re 5 6 (ℓ "伥") ∷
   re 0 6 (ℓ "侓") ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = wlE 518 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 519 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = sE 32 (lem-cQ-at032032 c4)
  q143 : Ws → Eqn
  q143 c4 = wlE 520 (lit c4)

-- box-tQ @032032: 13 steps
lem-box-tQ-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "亓亰亓亰") ⟫ʷ
lem-box-tQ-at032032 c4 = derive (ℓ "佪") (ℓ "亓亰亓亰")
  (re 0 1 (ℓ "亐亓伟亓亐伟") ∷
   re 2 1 (ℓ "交亥伛亥交伛") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q140 c4) ∷
   re 5 1 (ℓ "交亥伛亥交伛") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
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
  q148 c4 = sE 22 (lem-comm-SWAP02-BOX⟨3·14⟩ c4)

-- nat-SWbc @032032: 23 steps
lem-nat-SWbc-at032032 : Ws → ⟪ (ℓ "串佪串") ⟫ʷ ≈ ⟪ (ℓ "佬") ⟫ʷ
lem-nat-SWbc-at032032 c4 = derive (ℓ "串佪串") (ℓ "佬")
  (re 1 1 (ℓ "亐亓伟亓亐伟") ∷
   rw⁻ 0 (q144 c4) ∷
   rw 1 (q145 c4) ∷
   re 3 1 (ℓ "交亥伛亥交伛") ∷
   rw⁻ 2 (q146 c4) ∷
   rw 3 (q147 c4) ∷
   rw 4 (q148 c4) ∷
   rw 5 (q147 c4) ∷
   rw⁻ 6 (q146 c4) ∷
   rw 7 (q148 c4) ∷
   rw 8 (q145 c4) ∷
   rw⁻ 9 (q144 c4) ∷
   re 11 1 (ℓ "交亥伛亥交伛") ∷
   rw⁻ 10 (q146 c4) ∷
   rw 11 (q147 c4) ∷
   rw 12 (q148 c4) ∷
   rw 13 (q147 c4) ∷
   rw⁻ 14 (q146 c4) ∷
   rw 15 (q148 c4) ∷
   rw 16 (q124 c4) ∷
   re 2 6 (ℓ "伜") ∷
   re 5 6 (ℓ "伜") ∷
   re 0 6 (ℓ "佬") ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = wlE 539 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 540 (lit c4)

-- nat-SWbc @0330: 23 steps
lem-nat-SWbc-at0330 : Ws → ⟪ (ℓ "串佬串") ⟫ʷ ≈ ⟪ (ℓ "佪") ⟫ʷ
lem-nat-SWbc-at0330 c4 = derive (ℓ "串佬串") (ℓ "佪")
  (re 1 1 (ℓ "交产伜产交伜") ∷
   rw⁻ 0 (q146 c4) ∷
   rw 1 (q149 c4) ∷
   re 3 1 (ℓ "亐互伛互亐伛") ∷
   rw⁻ 2 (q144 c4) ∷
   rw 3 (q150 c4) ∷
   rw 4 (q148 c4) ∷
   rw 5 (q150 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw 7 (q148 c4) ∷
   rw 8 (q149 c4) ∷
   rw⁻ 9 (q146 c4) ∷
   re 11 1 (ℓ "亐互伛互亐伛") ∷
   rw⁻ 10 (q144 c4) ∷
   rw 11 (q150 c4) ∷
   rw 12 (q148 c4) ∷
   rw 13 (q150 c4) ∷
   rw⁻ 14 (q144 c4) ∷
   rw 15 (q148 c4) ∷
   rw 16 (q124 c4) ∷
   re 2 6 (ℓ "伟") ∷
   re 5 6 (ℓ "伟") ∷
   re 0 6 (ℓ "佪") ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = wpE 496 c4
  q152 : Ws → Eqn
  q152 c4 = wlE 611 (lit c4)

-- cQ @0214203143: 7 steps
lem-cQ-at0214203143 : Ws → ⟪ (ℓ "亜交") ⟫ʷ ≈ ⟪ (ℓ "交亜") ⟫ʷ
lem-cQ-at0214203143 c4 = derive (ℓ "亜交") (ℓ "交亜")
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
  q155 c4 = sE 21 (lem-comm-CX41-CCZ023 c4)
  q156 : Ws → Eqn
  q156 c4 = wlE 620 (lit c4)
  q157 : Ws → Eqn
  q157 c4 = wlE 621 (lit c4)

-- cQ @0214213043: 7 steps
lem-cQ-at0214213043 : Ws → ⟪ (ℓ "亨亘") ⟫ʷ ≈ ⟪ (ℓ "亘亨") ⟫ʷ
lem-cQ-at0214213043 c4 = derive (ℓ "亨亘") (ℓ "亘亨")
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
  q160 c4 = sE 18 (lem-comm-CX03-CCZ124 c4)
  q161 : Ws → Eqn
  q161 c4 = wlE 638 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = wlE 639 (lit c4)

-- cQ @0210233441: 7 steps
lem-cQ-at0210233441 : Ws → ⟪ (ℓ "亘亨") ⟫ʷ ≈ ⟪ (ℓ "亨亘") ⟫ʷ
lem-cQ-at0210233441 c4 = derive (ℓ "亘亨") (ℓ "亨亘")
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
lem-cQ-at14213243 : Ws → ⟪ (ℓ "五亘") ⟫ʷ ≈ ⟪ (ℓ "亘五") ⟫ʷ
lem-cQ-at14213243 c4 = derive (ℓ "五亘") (ℓ "亘五")
  (rw 0 (q163 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 3 (q155 c4) ∷
   rw⁻ 2 (q164 c4) ∷
   rw 1 (q155 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw⁻ 1 (q163 c4) ∷ []) Eq.refl

-- cQ @143143: 7 steps
lem-cQ-at143143 : Ws → ⟪ (ℓ "亜亐") ⟫ʷ ≈ ⟪ (ℓ "亐亜") ⟫ʷ
lem-cQ-at143143 c4 = derive (ℓ "亜亐") (ℓ "亐亜")
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
  q167 c4 = sE 24 (lem-comm-SWAP14-BOX⟨2·03⟩ c4)

-- nat-SWbc @0210243143: 23 steps
lem-nat-SWbc-at0210243143 : Ws → ⟪ (ℓ "乘伱乘") ⟫ʷ ≈ ⟪ (ℓ "伮") ⟫ʷ
lem-nat-SWbc-at0210243143 c4 = derive (ℓ "乘伱乘") (ℓ "伮")
  (re 1 1 (ℓ "亜亞仉亞亜仉") ∷
   rw⁻ 0 (q69 c4) ∷
   rw 1 (q165 c4) ∷
   re 3 1 (ℓ "二亍仈亍二仈") ∷
   rw⁻ 2 (q71 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q167 c4) ∷
   rw 5 (q166 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw 7 (q167 c4) ∷
   rw 8 (q165 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   re 11 1 (ℓ "二亍仈亍二仈") ∷
   rw⁻ 10 (q71 c4) ∷
   rw 11 (q166 c4) ∷
   rw 12 (q167 c4) ∷
   rw 13 (q166 c4) ∷
   rw⁻ 14 (q71 c4) ∷
   rw 15 (q167 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (ℓ "仜") ∷
   re 5 6 (ℓ "仜") ∷
   re 0 6 (ℓ "伮") ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = sE 30 (lem-cQ-at0210213443 c4)

-- tP @0210213443: 7 steps
lem-tP-at0210213443 : Ws → ⟪ (ℓ "亏亱") ⟫ʷ ≈ ⟪ (ℓ "亱亏") ⟫ʷ
lem-tP-at0210213443 c4 = derive (ℓ "亏亱") (ℓ "亱亏")
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
  q173 c4 = sE 28 (lem-comm-SWAP24-BOX⟨0·13⟩ c4)

-- nat-SWbc @243243: 23 steps
lem-nat-SWbc-at243243 : Ws → ⟪ (ℓ "乬仄乬") ⟫ʷ ≈ ⟪ (ℓ "亼") ⟫ʷ
lem-nat-SWbc-at243243 c4 = derive (ℓ "乬仄乬") (ℓ "亼")
  (re 1 1 (ℓ "五井仃井五仃") ∷
   rw⁻ 0 (q169 c4) ∷
   rw 1 (q170 c4) ∷
   re 3 1 (ℓ "二于人于二人") ∷
   rw⁻ 2 (q171 c4) ∷
   rw 3 (q172 c4) ∷
   rw 4 (q173 c4) ∷
   rw 5 (q172 c4) ∷
   rw⁻ 6 (q171 c4) ∷
   rw 7 (q173 c4) ∷
   rw 8 (q170 c4) ∷
   rw⁻ 9 (q169 c4) ∷
   re 11 1 (ℓ "二于人于二人") ∷
   rw⁻ 10 (q171 c4) ∷
   rw 11 (q172 c4) ∷
   rw 12 (q173 c4) ∷
   rw 13 (q172 c4) ∷
   rw⁻ 14 (q171 c4) ∷
   rw 15 (q173 c4) ∷
   rw 16 (q65 c4) ∷
   re 2 6 (ℓ "亻") ∷
   re 5 6 (ℓ "亻") ∷
   re 0 6 (ℓ "亼") ∷ []) Eq.refl

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
  q178 c4 = sE 27 (lem-comm-SWAP23-BOX⟨0·41⟩ c4)

-- nat-SWbc @1441: 23 steps
lem-nat-SWbc-at1441 : Ws → ⟪ (ℓ "乥伈乥") ⟫ʷ ≈ ⟪ (ℓ "伍") ⟫ʷ
lem-nat-SWbc-at1441 c4 = derive (ℓ "乥伈乥") (ℓ "伍")
  (re 1 1 (ℓ "亜亝伇亝亜伇") ∷
   rw⁻ 0 (q174 c4) ∷
   rw 1 (q175 c4) ∷
   re 3 1 (ℓ "亠亣价亣亠价") ∷
   rw⁻ 2 (q176 c4) ∷
   rw 3 (q177 c4) ∷
   rw 4 (q178 c4) ∷
   rw 5 (q177 c4) ∷
   rw⁻ 6 (q176 c4) ∷
   rw 7 (q178 c4) ∷
   rw 8 (q175 c4) ∷
   rw⁻ 9 (q174 c4) ∷
   re 11 1 (ℓ "亠亣价亣亠价") ∷
   rw⁻ 10 (q176 c4) ∷
   rw 11 (q177 c4) ∷
   rw 12 (q178 c4) ∷
   rw 13 (q177 c4) ∷
   rw⁻ 14 (q176 c4) ∷
   rw 15 (q178 c4) ∷
   rw 16 (q26 c4) ∷
   re 2 6 (ℓ "伌") ∷
   re 5 6 (ℓ "伌") ∷
   re 0 6 (ℓ "伍") ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = wpE 162 c4
  q180 : Ws → Eqn
  q180 c4 = sE 38 (lem-cQ-at14233241 c4)

-- box-tQ @14233241: 13 steps
lem-box-tQ-at14233241 : Ws → ⟪ (ℓ "伍") ⟫ʷ ≈ ⟪ (ℓ "亡二亡二") ⟫ʷ
lem-box-tQ-at14233241 c4 = derive (ℓ "伍") (ℓ "亡二亡二")
  (re 0 1 (ℓ "亠亡伌亡亠伌") ∷
   re 2 1 (ℓ "亜亟价亟亜价") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q179 c4) ∷
   re 5 1 (ℓ "亜亟价亟亜价") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q179 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q180 c4) ∷
   rw 2 (q31 c4) ∷ []) Eq.refl

-- tP @14233241: 7 steps
lem-tP-at14233241 : Ws → ⟪ (ℓ "亡亍") ⟫ʷ ≈ ⟪ (ℓ "亍亡") ⟫ʷ
lem-tP-at14233241 c4 = derive (ℓ "亡亍") (ℓ "亍亡")
  (rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q180 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q81 c4) ∷ []) Eq.refl

-- cQ @12213443: 7 steps
lem-cQ-at12213443 : Ws → ⟪ (ℓ "二亠") ⟫ʷ ≈ ⟪ (ℓ "亠二") ⟫ʷ
lem-cQ-at12213443 c4 = derive (ℓ "二亠") (ℓ "亠二")
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
lem-cQ-at0314213042 : Ws → ⟪ (ℓ "京亘") ⟫ʷ ≈ ⟪ (ℓ "亘京") ⟫ʷ
lem-cQ-at0314213042 c4 = derive (ℓ "京亘") (ℓ "亘京")
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
  q186 c4 = sE 19 (lem-comm-CX30-CCZ124 c4)
  q187 : Ws → Eqn
  q187 c4 = wpE 679 c4

-- cQ @0213203441: 7 steps
lem-cQ-at0213203441 : Ws → ⟪ (ℓ "亘亨") ⟫ʷ ≈ ⟪ (ℓ "亨亘") ⟫ʷ
lem-cQ-at0213203441 c4 = derive (ℓ "亘亨") (ℓ "亨亘")
  (rw 0 (q185 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   rw 3 (q186 c4) ∷
   rw⁻ 2 (q187 c4) ∷
   rw 1 (q186 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q185 c4) ∷ []) Eq.refl

-- tP @032032: 7 steps
lem-tP-at032032 : Ws → ⟪ (ℓ "亓亲") ⟫ʷ ≈ ⟪ (ℓ "亲亓") ⟫ʷ
lem-tP-at032032 c4 = derive (ℓ "亓亲") (ℓ "亲亓")
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
lem-cQ-at0312243140 : Ws → ⟪ (ℓ "亰亐") ⟫ʷ ≈ ⟪ (ℓ "亐亰") ⟫ʷ
lem-cQ-at0312243140 c4 = derive (ℓ "亰亐") (ℓ "亐亰")
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
  q196 c4 = sE 26 (lem-comm-SWAP14-BOX⟨3·20⟩ c4)

-- nat-SWbc @0312243140: 23 steps
lem-nat-SWbc-at0312243140 : Ws → ⟪ (ℓ "乘併乘") ⟫ʷ ≈ ⟪ (ℓ "佳") ⟫ʷ
lem-nat-SWbc-at0312243140 c4 = derive (ℓ "乘併乘") (ℓ "佳")
  (re 1 1 (ℓ "亰亲佃亲亰佃") ∷
   rw⁻ 0 (q192 c4) ∷
   rw 1 (q193 c4) ∷
   re 3 1 (ℓ "交亦佂亦交佂") ∷
   rw⁻ 2 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw 4 (q196 c4) ∷
   rw 5 (q195 c4) ∷
   rw⁻ 6 (q194 c4) ∷
   rw 7 (q196 c4) ∷
   rw 8 (q193 c4) ∷
   rw⁻ 9 (q192 c4) ∷
   re 11 1 (ℓ "交亦佂亦交佂") ∷
   rw⁻ 10 (q194 c4) ∷
   rw 11 (q195 c4) ∷
   rw 12 (q196 c4) ∷
   rw 13 (q195 c4) ∷
   rw⁻ 14 (q194 c4) ∷
   rw 15 (q196 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (ℓ "佉") ∷
   re 5 6 (ℓ "佉") ∷
   re 0 6 (ℓ "佳") ∷ []) Eq.refl

-- cQ @033440: 7 steps
lem-cQ-at033440 : Ws → ⟪ (ℓ "交亠") ⟫ʷ ≈ ⟪ (ℓ "亠交") ⟫ʷ
lem-cQ-at033440 c4 = derive (ℓ "交亠") (ℓ "亠交")
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
lem-cQ-at0312213440 : Ws → ⟪ (ℓ "交亠") ⟫ʷ ≈ ⟪ (ℓ "亠交") ⟫ʷ
lem-cQ-at0312213440 c4 = derive (ℓ "交亠") (ℓ "亠交")
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
lem-nat-SWbc-at0312213440 : Ws → ⟪ (ℓ "乘佳乘") ⟫ʷ ≈ ⟪ (ℓ "併") ⟫ʷ
lem-nat-SWbc-at0312213440 c4 = derive (ℓ "乘佳乘") (ℓ "併")
  (re 1 1 (ℓ "交产佉产交佉") ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q199 c4) ∷
   re 3 1 (ℓ "亰亱佂亱亰佂") ∷
   rw⁻ 2 (q192 c4) ∷
   rw 3 (q200 c4) ∷
   rw 4 (q196 c4) ∷
   rw 5 (q200 c4) ∷
   rw⁻ 6 (q192 c4) ∷
   rw 7 (q196 c4) ∷
   rw 8 (q199 c4) ∷
   rw⁻ 9 (q194 c4) ∷
   re 11 1 (ℓ "亰亱佂亱亰佂") ∷
   rw⁻ 10 (q192 c4) ∷
   rw 11 (q200 c4) ∷
   rw 12 (q196 c4) ∷
   rw 13 (q200 c4) ∷
   rw⁻ 14 (q192 c4) ∷
   rw 15 (q196 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (ℓ "佃") ∷
   re 5 6 (ℓ "佃") ∷
   re 0 6 (ℓ "併") ∷ []) Eq.refl

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
lem-cQ-at022330 : Ws → ⟪ (ℓ "交亜") ⟫ʷ ≈ ⟪ (ℓ "亜交") ⟫ʷ
lem-cQ-at022330 c4 = derive (ℓ "交亜") (ℓ "亜交")
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
  q206 c4 = sE 42 (lem-cQ-at0220 c4)
  q207 : Ws → Eqn
  q207 c4 = wlE 931 (lit c4)

-- box-tQ @0220: 13 steps
lem-box-tQ-at0220 : Ws → ⟪ (ℓ "伳") ⟫ʷ ≈ ⟪ (ℓ "亏亰亏亰") ⟫ʷ
lem-box-tQ-at0220 c4 = derive (ℓ "伳") (ℓ "亏亰亏亰")
  (re 0 1 (ℓ "二亏伕亏二伕") ∷
   re 2 1 (ℓ "交亥休亥交休") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q140 c4) ∷
   re 5 1 (ℓ "交亥休亥交休") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q140 c4) ∷
   rw 0 (q205 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q206 c4) ∷
   rw 2 (q207 c4) ∷ []) Eq.refl

-- tP @0220: 7 steps
lem-tP-at0220 : Ws → ⟪ (ℓ "亏亱") ⟫ʷ ≈ ⟪ (ℓ "亱亏") ⟫ʷ
lem-tP-at0220 c4 = derive (ℓ "亏亱") (ℓ "亱亏")
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
  q210 c4 = sE 41 (lem-cQ-at0213243140 c4)
  q211 : Ws → Eqn
  q211 c4 = wlE 937 (lit c4)

-- box-tQ @0213243140: 13 steps
lem-box-tQ-at0213243140 : Ws → ⟪ (ℓ "低") ⟫ʷ ≈ ⟪ (ℓ "亱二亱二") ⟫ʷ
lem-box-tQ-at0213243140 c4 = derive (ℓ "低") (ℓ "亱二亱二")
  (re 0 1 (ℓ "亰亱位亱亰位") ∷
   re 2 1 (ℓ "交产伷产交伷") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw⁻ 2 (q208 c4) ∷
   re 5 1 (ℓ "交产伷产交伷") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw⁻ 5 (q208 c4) ∷
   rw 0 (q209 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 1 (q210 c4) ∷
   rw 2 (q211 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = sE 25 (lem-comm-SWAP14-BOX⟨2·30⟩ c4)

-- nat-SWbc @0213243140: 23 steps
lem-nat-SWbc-at0213243140 : Ws → ⟪ (ℓ "乘低乘") ⟫ʷ ≈ ⟪ (ℓ "佈") ⟫ʷ
lem-nat-SWbc-at0213243140 c4 = derive (ℓ "乘低乘") (ℓ "佈")
  (re 1 1 (ℓ "亰亱位亱亰位") ∷
   rw⁻ 0 (q192 c4) ∷
   rw 1 (q200 c4) ∷
   re 3 1 (ℓ "交产伷产交伷") ∷
   rw⁻ 2 (q194 c4) ∷
   rw 3 (q199 c4) ∷
   rw 4 (q212 c4) ∷
   rw 5 (q199 c4) ∷
   rw⁻ 6 (q194 c4) ∷
   rw 7 (q212 c4) ∷
   rw 8 (q200 c4) ∷
   rw⁻ 9 (q192 c4) ∷
   re 11 1 (ℓ "交产伷产交伷") ∷
   rw⁻ 10 (q194 c4) ∷
   rw 11 (q199 c4) ∷
   rw 12 (q212 c4) ∷
   rw 13 (q199 c4) ∷
   rw⁻ 14 (q194 c4) ∷
   rw 15 (q212 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (ℓ "佇") ∷
   re 5 6 (ℓ "佇") ∷
   re 0 6 (ℓ "佈") ∷ []) Eq.refl

-- cQ @02233440: 7 steps
lem-cQ-at02233440 : Ws → ⟪ (ℓ "交亜") ⟫ʷ ≈ ⟪ (ℓ "亜交") ⟫ʷ
lem-cQ-at02233440 c4 = derive (ℓ "交亜") (ℓ "亜交")
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
lem-cQ-at0213213440 : Ws → ⟪ (ℓ "交亜") ⟫ʷ ≈ ⟪ (ℓ "亜交") ⟫ʷ
lem-cQ-at0213213440 c4 = derive (ℓ "交亜") (ℓ "亜交")
  (rw 0 (q213 c4) ∷
   rw⁻ 4 (q204 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 2 (q214 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 0 (q202 c4) ∷
   rw⁻ 1 (q213 c4) ∷ []) Eq.refl

-- nat-SWbc @0213213440: 23 steps
lem-nat-SWbc-at0213213440 : Ws → ⟪ (ℓ "乘佈乘") ⟫ʷ ≈ ⟪ (ℓ "低") ⟫ʷ
lem-nat-SWbc-at0213213440 c4 = derive (ℓ "乘佈乘") (ℓ "低")
  (re 1 1 (ℓ "交亦佇亦交佇") ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q195 c4) ∷
   re 3 1 (ℓ "亰亲伷亲亰伷") ∷
   rw⁻ 2 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q212 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 6 (q192 c4) ∷
   rw 7 (q212 c4) ∷
   rw 8 (q195 c4) ∷
   rw⁻ 9 (q194 c4) ∷
   re 11 1 (ℓ "亰亲伷亲亰伷") ∷
   rw⁻ 10 (q192 c4) ∷
   rw 11 (q193 c4) ∷
   rw 12 (q212 c4) ∷
   rw 13 (q193 c4) ∷
   rw⁻ 14 (q192 c4) ∷
   rw 15 (q212 c4) ∷
   rw 16 (q54 c4) ∷
   re 2 6 (ℓ "位") ∷
   re 5 6 (ℓ "位") ∷
   re 0 6 (ℓ "低") ∷ []) Eq.refl

-- tP @0213243140: 7 steps
lem-tP-at0213243140 : Ws → ⟪ (ℓ "亱亏") ⟫ʷ ≈ ⟪ (ℓ "亏亱") ⟫ʷ
lem-tP-at0213243140 c4 = derive (ℓ "亱亏") (ℓ "亏亱")
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
lem-nat-SWbc-at122331 : Ws → ⟪ (ℓ "乑仕乑") ⟫ʷ ≈ ⟪ (ℓ "仌") ⟫ʷ
lem-nat-SWbc-at122331 c4 = derive (ℓ "乑仕乑") (ℓ "仌")
  (re 1 1 (ℓ "亘亙仔亙亘仔") ∷
   rw⁻ 0 (q38 c4) ∷
   rw 1 (q215 c4) ∷
   re 3 1 (ℓ "二亏今亏二今") ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q216 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q216 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q215 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   re 11 1 (ℓ "二亏今亏二今") ∷
   rw⁻ 10 (q36 c4) ∷
   rw 11 (q216 c4) ∷
   rw 12 (q40 c4) ∷
   rw 13 (q216 c4) ∷
   rw⁻ 14 (q36 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q41 c4) ∷
   re 2 6 (ℓ "介") ∷
   re 5 6 (ℓ "介") ∷
   re 0 6 (ℓ "仌") ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = wlE 1023 (lit c4)
  q218 : Ws → Eqn
  q218 c4 = wlE 1024 (lit c4)

-- nat-SWbc @2332: 23 steps
lem-nat-SWbc-at2332 : Ws → ⟪ (ℓ "乥亾乥") ⟫ʷ ≈ ⟪ (ℓ "亹") ⟫ʷ
lem-nat-SWbc-at2332 c4 = derive (ℓ "乥亾乥") (ℓ "亹")
  (re 1 1 (ℓ "亐云亽云亐亽") ∷
   rw⁻ 0 (q23 c4) ∷
   rw 1 (q217 c4) ∷
   re 3 1 (ℓ "二于亷于二亷") ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q218 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q218 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 7 (q25 c4) ∷
   rw 8 (q217 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   re 11 1 (ℓ "二于亷于二亷") ∷
   rw⁻ 10 (q21 c4) ∷
   rw 11 (q218 c4) ∷
   rw 12 (q25 c4) ∷
   rw 13 (q218 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw 15 (q25 c4) ∷
   rw 16 (q26 c4) ∷
   re 2 6 (ℓ "亸") ∷
   re 5 6 (ℓ "亸") ∷
   re 0 6 (ℓ "亹") ∷ []) Eq.refl

-- box-tQ @0210213443: 13 steps
lem-box-tQ-at0210213443 : Ws → ⟪ (ℓ "伮") ⟫ʷ ≈ ⟪ (ℓ "亏亰亏亰") ⟫ʷ
lem-box-tQ-at0210213443 c4 = derive (ℓ "伮") (ℓ "亏亰亏亰")
  (re 0 1 (ℓ "二亏仜亏二仜") ∷
   re 2 1 (ℓ "亜亝仈亝亜仈") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw 2 (q130 c4) ∷
   re 5 1 (ℓ "亜亝仈亝亜仈") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw 5 (q130 c4) ∷
   rw 0 (q205 c4) ∷
   rw 2 (q132 c4) ∷
   rw 1 (q168 c4) ∷
   rw 2 (q207 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = sE 40 (lem-sym-ab-at03102132 c4)

-- box-perm-2134 @03102132: 1 steps
lem-box-perm-2134-at03102132 : Ws → ⟪ (ℓ "佤") ⟫ʷ ≈ ⟪ (ℓ "佪") ⟫ʷ
lem-box-perm-2134-at03102132 c4 = derive (ℓ "佤") (ℓ "佪")
  (rw 0 (q219 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = wpE 280 c4

-- box-tQ @03102132: 13 steps
lem-box-tQ-at03102132 : Ws → ⟪ (ℓ "佤") ⟫ʷ ≈ ⟪ (ℓ "亓亰亓亰") ⟫ʷ
lem-box-tQ-at03102132 c4 = derive (ℓ "佤") (ℓ "亓亰亓亰")
  (re 0 1 (ℓ "亐亓仮亓亐仮") ∷
   re 2 1 (ℓ "亘亙以亙亘以") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q220 c4) ∷
   re 5 1 (ℓ "亘亙以亙亘以") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
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
  q225 c4 = sE 23 (lem-comm-SWAP12-BOX⟨3·04⟩ c4)
  q226 : Ws → Eqn
  q226 c4 = wlE 6 (lit c4)

-- nat-SWbc @03102132: 23 steps
lem-nat-SWbc-at03102132 : Ws → ⟪ (ℓ "乊佤乊") ⟫ʷ ≈ ⟪ (ℓ "佦") ⟫ʷ
lem-nat-SWbc-at03102132 c4 = derive (ℓ "乊佤乊") (ℓ "佦")
  (re 1 1 (ℓ "亐亓仮亓亐仮") ∷
   rw⁻ 0 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   re 3 1 (ℓ "亘亙以亙亘以") ∷
   rw⁻ 2 (q223 c4) ∷
   rw 3 (q224 c4) ∷
   rw 4 (q225 c4) ∷
   rw 5 (q224 c4) ∷
   rw⁻ 6 (q223 c4) ∷
   rw 7 (q225 c4) ∷
   rw 8 (q222 c4) ∷
   rw⁻ 9 (q221 c4) ∷
   re 11 1 (ℓ "亘亙以亙亘以") ∷
   rw⁻ 10 (q223 c4) ∷
   rw 11 (q224 c4) ∷
   rw 12 (q225 c4) ∷
   rw 13 (q224 c4) ∷
   rw⁻ 14 (q223 c4) ∷
   rw 15 (q225 c4) ∷
   rw 16 (q226 c4) ∷
   re 2 6 (ℓ "仦") ∷
   re 5 6 (ℓ "仦") ∷
   re 0 6 (ℓ "佦") ∷ []) Eq.refl

private
  q227 : Ws → Eqn
  q227 c4 = wlE 220 (lit c4)
  q228 : Ws → Eqn
  q228 c4 = wpE 820 c4

-- cQ @022440: 7 steps
lem-cQ-at022440 : Ws → ⟪ (ℓ "亨亘") ⟫ʷ ≈ ⟪ (ℓ "亘亨") ⟫ʷ
lem-cQ-at022440 c4 = derive (ℓ "亨亘") (ℓ "亘亨")
  (rw 0 (q227 c4) ∷
   rw⁻ 4 (q157 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 2 (q228 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 0 (q154 c4) ∷
   rw⁻ 1 (q227 c4) ∷ []) Eq.refl

-- cQ @02102441: 7 steps
lem-cQ-at02102441 : Ws → ⟪ (ℓ "亜交") ⟫ʷ ≈ ⟪ (ℓ "交亜") ⟫ʷ
lem-cQ-at02102441 c4 = derive (ℓ "亜交") (ℓ "交亜")
  (rw 0 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q6 c4) ∷ []) Eq.refl
