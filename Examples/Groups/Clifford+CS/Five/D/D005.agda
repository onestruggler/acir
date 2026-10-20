{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-cQ-at021021 ; lem-sym-ab-at0210243143 ; lem-sym-ab-at032032 ; lem-sym-ab-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-cQ-at0213243041 ; lem-cQ-at0214233041 ; lem-cQ-at0310213442 ; lem-sym-ab-at021021 ; lem-sym-ab-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-cQ-at03203442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX02-CCZ134 ; lem-comm-CX04-CCZ123 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-CCZ013 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CX42-CCZ013 ; lem-comm-SWAP13-BOX⟨0·42⟩ ; lem-comm-SWAP14-BOX⟨0·23⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX03-CCZ124 ; lem-comm-CX30-CCZ124 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-SWAP12-BOX⟨3·04⟩ ; lem-comm-SWAP12-BOX⟨3·40⟩ ; lem-comm-SWAP14-BOX⟨2·03⟩ ; lem-comm-SWAP23-BOX⟨0·41⟩ ; lem-comm-SWAP24-BOX⟨0·13⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX20-CCZ134 ; lem-comm-SWAP02-BOX⟨3·41⟩ ; lem-comm-SWAP03-BOX⟨4·21⟩ ; lem-comm-SWAP04-BOX⟨3·21⟩ ; lem-comm-SWAP12-BOX⟨4·03⟩ ; lem-comm-SWAP13-BOX⟨2·04⟩ ; lem-comm-SWAP14-BOX⟨3·02⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-SWAP12-BOX⟨4·30⟩ ; lem-comm-SWAP13-BOX⟨4·20⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ024 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ012 ∷ []) (wp 196 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sw14 ∷ Toff012 ∷ []) (Toff024 ∷ Sw14 ∷ []) (wp 570 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ012 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ024 ∷ []) (wp 194 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Sw14 ∷ Toff204 ∷ []) (Toff201 ∷ Sw14 ∷ []) (wp 569 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Sw14 ∷ Bx0-23 ∷ []) (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Sw14 ∷ Sw14 ∷ []) [] (wl 306 (lit c4))

-- nat-SWbc @12213443: 23 steps
lem-nat-SWbc-at12213443 : Ws → ⟪ (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-nat-SWbc-at12213443 c4 = derive (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (Bx0-2413 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   re 3 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 11 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q4 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q6 c4) ∷
   re 2 6 (Bx2-013 ∷ []) ∷
   re 5 6 (Bx2-013 ∷ []) ∷
   re 0 6 (Bx0-2413 ∷ []) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ024 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ034 ∷ []) (wp 596 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (wp 986 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ034 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ024 ∷ []) (wp 594 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ []) (wp 987 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Sw23 ∷ Bx0-41 ∷ []) (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 (lit c4))

-- nat-SWbc @14233241: 23 steps
lem-nat-SWbc-at14233241 : Ws → ⟪ (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-nat-SWbc-at14233241 c4 = derive (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (Bx0-4231 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   re 3 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q8 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 11 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   rw⁻ 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q10 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q12 c4) ∷
   re 2 6 (Bx4-031 ∷ []) ∷
   re 5 6 (Bx4-031 ∷ []) ∷
   re 0 6 (Bx0-4231 ∷ []) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl 675 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ013 ∷ CS34 ∷ []) (CS34 ∷ CCZ013 ∷ []) (wp 185 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CX42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ013 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ013 ∷ []) (wl 1167 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) (wl 324 (lit c4))

-- cQ @03143140: 7 steps
lem-cQ-at03143140 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at03143140 c4 = derive (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  (rw 0 (q13 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl 37 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl 38 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl 44 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl 84 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw12 ∷ Bx3-40 ∷ []) (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 (lit c4))

-- nat-SWbc @03143140: 23 steps
lem-nat-SWbc-at03143140 : Ws → ⟪ (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-nat-SWbc-at03143140 c4 = derive (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (Bx3-4120 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) ∷
   rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   re 3 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 7 (q22 c4) ∷
   rw 8 (q19 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   re 11 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   rw⁻ 10 (q20 c4) ∷
   rw 11 (q21 c4) ∷
   rw 12 (q22 c4) ∷
   rw 13 (q21 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw 15 (q22 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (Bx4-320 ∷ []) ∷
   re 5 6 (Bx4-320 ∷ []) ∷
   re 0 6 (Bx3-4120 ∷ []) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl 617 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ023 ∷ CS34 ∷ []) (CS34 ∷ CCZ023 ∷ []) (wp 543 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ023 ∷ []) (wl 669 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) (wl 670 (lit c4))

-- cQ @0314213240: 7 steps
lem-cQ-at0314213240 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0314213240 c4 = derive (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  (rw 0 (q24 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 0 (q28 c4) ∷
   rw⁻ 1 (q24 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl 698 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ023 ∷ []) (wp 574 c4)

-- cQ @03243240: 7 steps
lem-cQ-at03243240 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at03243240 c4 = derive (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  (rw 0 (q29 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 3 (q30 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   rw 1 (q30 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw⁻ 1 (q29 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl 45 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl 85 (lit c4))

-- nat-SWbc @0314213240: 23 steps
lem-nat-SWbc-at0314213240 : Ws → ⟪ (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314213240 c4 = derive (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (Bx3-4210 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) ∷
   rw⁻ 0 (q20 c4) ∷
   rw 1 (q32 c4) ∷
   re 3 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   rw⁻ 2 (q18 c4) ∷
   rw 3 (q33 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw 7 (q22 c4) ∷
   rw 8 (q32 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   re 11 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 11 (q33 c4) ∷
   rw 12 (q22 c4) ∷
   rw 13 (q33 c4) ∷
   rw⁻ 14 (q18 c4) ∷
   rw 15 (q22 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (Bx4-310 ∷ []) ∷
   re 5 6 (Bx4-310 ∷ []) ∷
   re 0 6 (Bx3-4210 ∷ []) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl 458 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ134 ∷ CS03 ∷ []) (CS03 ∷ CCZ134 ∷ []) (wp 706 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CX02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ134 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ134 ∷ []) (wl 1237 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ []) (wl 790 (lit c4))

-- cQ @03103441: 7 steps
lem-cQ-at03103441 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at03103441 c4 = derive (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  (rw 0 (q34 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q38 c4) ∷
   rw⁻ 1 (q34 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp 352 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ []) (wl 490 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CX04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ123 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ123 ∷ []) (wl 491 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ123 ∷ CS34 ∷ []) (CS34 ∷ CCZ123 ∷ []) (wl 492 (lit c4))

-- cQ @0310243241: 7 steps
lem-cQ-at0310243241 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0310243241 c4 = derive (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  (rw 0 (q39 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw⁻ 1 (q39 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ013 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ034 ∷ []) (wp 149 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Sw14 ∷ Toff304 ∷ []) (Toff301 ∷ Sw14 ∷ []) (wp 289 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ034 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ013 ∷ []) (wp 151 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Sw14 ∷ Toff013 ∷ []) (Toff034 ∷ Sw14 ∷ []) (wp 288 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (Sw14 ∷ Bx3-02 ∷ []) (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4))

-- nat-SWbc @0310243142: 23 steps
lem-nat-SWbc-at0310243142 : Ws → ⟪ (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-nat-SWbc-at0310243142 c4 = derive (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (Bx3-0142 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   rw⁻ 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   re 3 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q48 c4) ∷
   rw 5 (q47 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw 7 (q48 c4) ∷
   rw 8 (q45 c4) ∷
   rw⁻ 9 (q44 c4) ∷
   re 11 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   rw⁻ 10 (q46 c4) ∷
   rw 11 (q47 c4) ∷
   rw 12 (q48 c4) ∷
   rw 13 (q47 c4) ∷
   rw⁻ 14 (q46 c4) ∷
   rw 15 (q48 c4) ∷
   rw 16 (q6 c4) ∷
   re 2 6 (Bx0-342 ∷ []) ∷
   re 5 6 (Bx0-342 ∷ []) ∷
   re 0 6 (Bx3-0142 ∷ []) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (CCZ234 ∷ []) (wp 1068 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ013 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) (wl 519 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CZ01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at0310213442 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ013 ∷ CZ01 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ []) (wl 520 (lit c4))

-- box-tQ @0310213442: 13 steps
lem-box-tQ-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q49 c4) ∷
   re 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q49 c4) ∷
   rw 0 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (Sw14 ∷ Toff301 ∷ []) (Toff304 ∷ Sw14 ∷ []) (wp 152 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Sw14 ∷ Toff034 ∷ []) (Toff013 ∷ Sw14 ∷ []) (wp 150 c4)

-- nat-SWbc @0310213442: 23 steps
lem-nat-SWbc-at0310213442 : Ws → ⟪ (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-nat-SWbc-at0310213442 c4 = derive (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (Bx3-0412 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) ∷
   rw⁻ 0 (q46 c4) ∷
   rw 1 (q54 c4) ∷
   re 3 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q48 c4) ∷
   rw 5 (q55 c4) ∷
   rw⁻ 6 (q44 c4) ∷
   rw 7 (q48 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   re 11 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   rw⁻ 10 (q44 c4) ∷
   rw 11 (q55 c4) ∷
   rw 12 (q48 c4) ∷
   rw 13 (q55 c4) ∷
   rw⁻ 14 (q44 c4) ∷
   rw 15 (q48 c4) ∷
   rw 16 (q6 c4) ∷
   re 2 6 (Bx0-312 ∷ []) ∷
   re 5 6 (Bx0-312 ∷ []) ∷
   re 0 6 (Bx3-0412 ∷ []) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl 1270 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CX20 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ134 ∷ []) (wp 704 c4)

-- cQ @0312203441: 7 steps
lem-cQ-at0312203441 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0312203441 c4 = derive (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  (rw 0 (q56 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q56 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ234 ∷ Sw04 ∷ []) (Sw04 ∷ CCZ023 ∷ []) (wp 1089 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Sw04 ∷ Toff302 ∷ []) (Toff324 ∷ Sw04 ∷ []) (wp 1090 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ023 ∷ Sw04 ∷ []) (Sw04 ∷ CCZ234 ∷ []) (wp 1091 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw04 ∷ Toff234 ∷ []) (Toff203 ∷ Sw04 ∷ []) (wp 1092 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw04 ∷ Bx3-21 ∷ []) (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Sw04 ∷ Sw04 ∷ []) [] (wp 1093 c4)

-- nat-SWbc @0312203441: 23 steps
lem-nat-SWbc-at0312203441 : Ws → ⟪ (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312203441 c4 = derive (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (Bx3-2401 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) ∷
   rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   re 3 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 7 (q63 c4) ∷
   rw 8 (q60 c4) ∷
   rw⁻ 9 (q59 c4) ∷
   re 11 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   rw⁻ 10 (q61 c4) ∷
   rw 11 (q62 c4) ∷
   rw 12 (q63 c4) ∷
   rw 13 (q62 c4) ∷
   rw⁻ 14 (q61 c4) ∷
   rw 15 (q63 c4) ∷
   rw 16 (q64 c4) ∷
   re 2 6 (Bx2-301 ∷ []) ∷
   re 5 6 (Bx2-301 ∷ []) ∷
   re 0 6 (Bx3-2401 ∷ []) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl 245 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CX24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ013 ∷ []) (wp 184 c4)

-- cQ @0312243041: 7 steps
lem-cQ-at0312243041 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0312243041 c4 = derive (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  (rw 0 (q65 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q66 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q66 c4) ∷
   rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q65 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw04 ∷ Toff324 ∷ []) (Toff302 ∷ Sw04 ∷ []) (wp 1103 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (Sw04 ∷ Toff203 ∷ []) (Toff234 ∷ Sw04 ∷ []) (wp 1104 c4)

-- nat-SWbc @0312243041: 23 steps
lem-nat-SWbc-at0312243041 : Ws → ⟪ (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312243041 c4 = derive (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (Bx3-2041 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) ∷
   rw⁻ 0 (q61 c4) ∷
   rw 1 (q68 c4) ∷
   re 3 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   rw⁻ 2 (q59 c4) ∷
   rw 3 (q69 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 6 (q59 c4) ∷
   rw 7 (q63 c4) ∷
   rw 8 (q68 c4) ∷
   rw⁻ 9 (q61 c4) ∷
   re 11 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   rw⁻ 10 (q59 c4) ∷
   rw 11 (q69 c4) ∷
   rw 12 (q63 c4) ∷
   rw 13 (q69 c4) ∷
   rw⁻ 14 (q59 c4) ∷
   rw 15 (q63 c4) ∷
   rw 16 (q64 c4) ∷
   re 2 6 (Bx2-341 ∷ []) ∷
   re 5 6 (Bx2-341 ∷ []) ∷
   re 0 6 (Bx3-2041 ∷ []) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ014 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ012 ∷ []) (wp 584 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Sw24 ∷ Toff012 ∷ []) (Toff014 ∷ Sw24 ∷ []) (wp 1116 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ012 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ014 ∷ []) (wp 582 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw24 ∷ Toff104 ∷ []) (Toff102 ∷ Sw24 ∷ []) (wp 1117 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw24 ∷ Bx0-13 ∷ []) (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (Sw24 ∷ Sw24 ∷ []) [] (wl 322 (lit c4))

-- nat-SWbc @3443: 23 steps
lem-nat-SWbc-at3443 : Ws → ⟪ (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-nat-SWbc-at3443 c4 = derive (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (Bx0-1423 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) ∷
   rw⁻ 0 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   re 3 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 7 (q74 c4) ∷
   rw 8 (q71 c4) ∷
   rw⁻ 9 (q70 c4) ∷
   re 11 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   rw⁻ 10 (q72 c4) ∷
   rw 11 (q73 c4) ∷
   rw 12 (q74 c4) ∷
   rw 13 (q73 c4) ∷
   rw⁻ 14 (q72 c4) ∷
   rw 15 (q74 c4) ∷
   rw 16 (q75 c4) ∷
   re 2 6 (Bx1-023 ∷ []) ∷
   re 5 6 (Bx1-023 ∷ []) ∷
   re 0 6 (Bx0-1423 ∷ []) ∷ []) Eq.refl

-- cQ @03122031: 7 steps
lem-cQ-at03122031 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at03122031 c4 = derive (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  (rw 0 (q56 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q56 c4) ∷ []) Eq.refl

-- cQ @031031: 7 steps
lem-cQ-at031031 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at031031 c4 = derive (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  (rw 0 (q34 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q38 c4) ∷
   rw⁻ 1 (q34 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ013 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ023 ∷ []) (wl 838 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (wl 877 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ023 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ013 ∷ []) (wl 840 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (wl 876 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (Sw12 ∷ Bx3-04 ∷ []) (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4))

-- nat-SWbc @031031: 23 steps
lem-nat-SWbc-at031031 : Ws → ⟪ (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-nat-SWbc-at031031 c4 = derive (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (Bx3-0124 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) ∷
   rw⁻ 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   re 3 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   rw⁻ 2 (q78 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q80 c4) ∷
   rw 5 (q79 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 7 (q80 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   re 11 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   rw⁻ 10 (q78 c4) ∷
   rw 11 (q79 c4) ∷
   rw 12 (q80 c4) ∷
   rw 13 (q79 c4) ∷
   rw⁻ 14 (q78 c4) ∷
   rw 15 (q80 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (Bx0-324 ∷ []) ∷
   re 5 6 (Bx0-324 ∷ []) ∷
   re 0 6 (Bx3-0124 ∷ []) ∷ []) Eq.refl

-- cQ @03143041: 7 steps
lem-cQ-at03143041 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at03143041 c4 = derive (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  (rw 0 (q13 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ034 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ234 ∷ []) (wp 1146 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Sw02 ∷ Toff324 ∷ []) (Toff304 ∷ Sw02 ∷ []) (wp 1147 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ234 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ034 ∷ []) (wp 1148 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Sw02 ∷ Toff403 ∷ []) (Toff423 ∷ Sw02 ∷ []) (wp 1149 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Sw02 ∷ Bx3-41 ∷ []) (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw02 ∷ Sw02 ∷ []) [] (wl 485 (lit c4))

-- nat-SWbc @03143041: 23 steps
lem-nat-SWbc-at03143041 : Ws → ⟪ (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-nat-SWbc-at03143041 c4 = derive (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (Bx3-4021 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) ∷
   rw⁻ 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   re 3 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   rw 7 (q85 c4) ∷
   rw 8 (q82 c4) ∷
   rw⁻ 9 (q81 c4) ∷
   re 11 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   rw⁻ 10 (q83 c4) ∷
   rw 11 (q84 c4) ∷
   rw 12 (q85 c4) ∷
   rw 13 (q84 c4) ∷
   rw⁻ 14 (q83 c4) ∷
   rw 15 (q85 c4) ∷
   rw 16 (q86 c4) ∷
   re 2 6 (Bx4-321 ∷ []) ∷
   re 5 6 (Bx4-321 ∷ []) ∷
   re 0 6 (Bx3-4021 ∷ []) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp 320 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ []) (wl 495 (lit c4))

-- cQ @0314203241: 7 steps
lem-cQ-at0314203241 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0314203241 c4 = derive (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  (rw 0 (q87 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 0 (q40 c4) ∷
   rw⁻ 1 (q87 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp 496 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ123 ∷ CS24 ∷ []) (CS24 ∷ CCZ123 ∷ []) (wl 173 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ123 ∷ []) (wl 611 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) (wl 171 (lit c4))

-- cQ @02142041: 7 steps
lem-cQ-at02142041 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at02142041 c4 = derive (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  (rw 0 (q90 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q92 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 0 (q93 c4) ∷
   rw⁻ 1 (q90 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) (wl 417 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) (wl 416 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (K2⁻ ∷ K2 ∷ []) [] (wl 175 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0214233041 c4)

-- tP @0214233041: 7 steps
lem-tP-at0214233041 : Ws → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0214233041 c4 = derive (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  (rw⁻ 0 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q94 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw02 ∷ Toff304 ∷ []) (Toff324 ∷ Sw02 ∷ []) (wp 1162 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw02 ∷ Toff423 ∷ []) (Toff403 ∷ Sw02 ∷ []) (wp 1163 c4)

-- nat-SWbc @0314203241: 23 steps
lem-nat-SWbc-at0314203241 : Ws → ⟪ (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314203241 c4 = derive (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (Bx3-4201 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) ∷
   rw⁻ 0 (q83 c4) ∷
   rw 1 (q98 c4) ∷
   re 3 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   rw⁻ 2 (q81 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q99 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw 7 (q85 c4) ∷
   rw 8 (q98 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   re 11 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   rw⁻ 10 (q81 c4) ∷
   rw 11 (q99 c4) ∷
   rw 12 (q85 c4) ∷
   rw 13 (q99 c4) ∷
   rw⁻ 14 (q81 c4) ∷
   rw 15 (q85 c4) ∷
   rw 16 (q86 c4) ∷
   re 2 6 (Bx4-301 ∷ []) ∷
   re 5 6 (Bx4-301 ∷ []) ∷
   re 0 6 (Bx3-4201 ∷ []) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp 162 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ234 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) (wl 936 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ012 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CZ))
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ234 ∷ CZ34 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ []) (wl 937 (lit c4))

-- box-tQ @0214233041: 13 steps
lem-box-tQ-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0214233041 c4 = derive (Bx2-4301 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q100 c4) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q100 c4) ∷
   rw 0 (q101 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q103 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw14 ∷ Toff201 ∷ []) (Toff204 ∷ Sw14 ∷ []) (wp 197 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw14 ∷ Toff024 ∷ []) (Toff012 ∷ Sw14 ∷ []) (wp 195 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (Sw14 ∷ Bx2-03 ∷ []) (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4))

-- nat-SWbc @0210213443: 23 steps
lem-nat-SWbc-at0210213443 : Ws → ⟪ (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210213443 c4 = derive (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (Bx2-0413 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q104 c4) ∷
   re 3 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q106 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw 7 (q106 c4) ∷
   rw 8 (q104 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 11 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 11 (q105 c4) ∷
   rw 12 (q106 c4) ∷
   rw 13 (q105 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw 15 (q106 c4) ∷
   rw 16 (q6 c4) ∷
   re 2 6 (Bx0-213 ∷ []) ∷
   re 5 6 (Bx0-213 ∷ []) ∷
   re 0 6 (Bx2-0413 ∷ []) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl 297 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp 92 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp 87 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)

-- cQ @02132130: 7 steps
lem-cQ-at02132130 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at02132130 c4 = derive (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  (rw 0 (q107 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 2 (q110 c4) ∷
   rw 1 (q109 c4) ∷
   rw⁻ 0 (q111 c4) ∷
   rw⁻ 1 (q107 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl 757 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ124 ∷ CS23 ∷ []) (CS23 ∷ CCZ124 ∷ []) (wl 639 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (CX30 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ124 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ124 ∷ []) (wp 679 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CCZ124 ∷ CS02 ∷ []) (CS02 ∷ CCZ124 ∷ []) (wp 515 c4)

-- cQ @02132031: 7 steps
lem-cQ-at02132031 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at02132031 c4 = derive (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  (rw 0 (q112 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 2 (q115 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q112 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = eqn (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (Toff301 ∷ []) (wl 434 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl 435 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (K3⁻ ∷ K3 ∷ []) [] (wl 436 (lit c4))

-- tP @0310213442: 7 steps
lem-tP-at0310213442 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at0310213442 c4 = derive (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  (rw⁻ 0 (q117 c4) ∷
   rw⁻ 3 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 0 (q118 c4) ∷
   rw 1 (q117 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = eqn (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243041 c4)

-- tP @0213243041: 7 steps
lem-tP-at0213243041 : Ws → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0213243041 c4 = derive (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  (rw⁻ 0 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q120 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q94 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl 288 (lit c4))

-- box-tQ @0213243041: 13 steps
lem-box-tQ-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0213243041 c4 = derive (Bx2-3401 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q121 c4) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q121 c4) ∷
   rw 0 (q101 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q103 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) (wp 280 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CCZ012 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (wl 930 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at021021 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ012 ∷ CZ01 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ []) (wl 931 (lit c4))

-- box-tQ @021021: 13 steps
lem-box-tQ-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at021021 c4 = derive (Bx2-0134 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q122 c4) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q122 c4) ∷
   rw 0 (q123 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q125 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl 326 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp 314 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (CX21 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ034 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ034 ∷ []) (wp 734 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) (wp 312 c4)

-- cQ @03122130: 7 steps
lem-cQ-at03122130 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at03122130 c4 = derive (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  (rw 0 (q126 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw 3 (q128 c4) ∷
   rw⁻ 2 (q129 c4) ∷
   rw 1 (q128 c4) ∷
   rw⁻ 0 (q130 c4) ∷
   rw⁻ 1 (q126 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Bx0-2134 ∷ []) (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4)

-- box-perm-2134 @1221: 1 steps
lem-box-perm-2134-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-2134-at1221 c4 = derive (Bx0-2134 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q131 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = eqn (Bx2-0134 ∷ []) (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4)

-- box-perm-2134 @021021: 1 steps
lem-box-perm-2134-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-box-perm-2134-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-1034 ∷ [])
  (rw 0 (q132 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) (CCZ234 ∷ []) (wl 1379 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at03203442 c4)

-- box-tQ @03203442: 13 steps
lem-box-tQ-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at03203442 c4 = derive (Bx3-1042 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q133 c4) ∷
   re 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q133 c4) ∷
   rw 0 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q134 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = eqn (Bx2-1034 ∷ []) (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4)

-- box-perm-2134 @0220: 1 steps
lem-box-perm-2134-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2134-at0220 c4 = derive (Bx2-1034 ∷ []) (Bx2-0134 ∷ [])
  (rw 0 (q135 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ023 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ012 ∷ []) (wl 283 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (Sw13 ∷ Toff201 ∷ []) (Toff203 ∷ Sw13 ∷ []) (wl 990 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ012 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ023 ∷ []) (wl 285 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (Sw13 ∷ Toff023 ∷ []) (Toff012 ∷ Sw13 ∷ []) (wl 989 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (Sw13 ∷ Bx2-04 ∷ []) (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (Sw13 ∷ Sw13 ∷ []) [] (wl 287 (lit c4))

-- nat-SWbc @021021: 23 steps
lem-nat-SWbc-at021021 : Ws → ⟪ (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-nat-SWbc-at021021 c4 = derive (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (Bx2-0314 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) ∷
   rw⁻ 0 (q136 c4) ∷
   rw 1 (q137 c4) ∷
   re 3 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 2 (q138 c4) ∷
   rw 3 (q139 c4) ∷
   rw 4 (q140 c4) ∷
   rw 5 (q139 c4) ∷
   rw⁻ 6 (q138 c4) ∷
   rw 7 (q140 c4) ∷
   rw 8 (q137 c4) ∷
   rw⁻ 9 (q136 c4) ∷
   re 11 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 10 (q138 c4) ∷
   rw 11 (q139 c4) ∷
   rw 12 (q140 c4) ∷
   rw 13 (q139 c4) ∷
   rw⁻ 14 (q138 c4) ∷
   rw 15 (q140 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (Bx0-214 ∷ []) ∷
   re 5 6 (Bx0-214 ∷ []) ∷
   re 0 6 (Bx2-0314 ∷ []) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl 637 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (CX03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ124 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ124 ∷ []) (wl 638 (lit c4))

-- cQ @02102331: 7 steps
lem-cQ-at02102331 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at02102331 c4 = derive (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  (rw 0 (q142 c4) ∷
   rw⁻ 4 (q116 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 2 (q144 c4) ∷
   rw 1 (q143 c4) ∷
   rw⁻ 0 (q113 c4) ∷
   rw⁻ 1 (q142 c4) ∷ []) Eq.refl

-- cQ @03243042: 7 steps
lem-cQ-at03243042 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at03243042 c4 = derive (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  (rw 0 (q29 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 3 (q30 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   rw 1 (q30 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw⁻ 1 (q29 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp 540 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ []) (wp 48 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ023 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ023 ∷ []) (wl 667 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) (wl 199 (lit c4))

-- cQ @142142: 7 steps
lem-cQ-at142142 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at142142 c4 = derive (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  (rw 0 (q145 c4) ∷
   rw⁻ 4 (q146 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 2 (q147 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 0 (q148 c4) ∷
   rw⁻ 1 (q145 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ034 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ014 ∷ []) (wp 208 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw13 ∷ Toff014 ∷ []) (Toff034 ∷ Sw13 ∷ []) (wp 1237 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ014 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ034 ∷ []) (wp 206 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Sw13 ∷ Toff403 ∷ []) (Toff401 ∷ Sw13 ∷ []) (wp 1238 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (Sw13 ∷ Bx0-42 ∷ []) (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4))

-- nat-SWbc @142142: 23 steps
lem-nat-SWbc-at142142 : Ws → ⟪ (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-nat-SWbc-at142142 c4 = derive (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) (Bx0-4312 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   re 3 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   rw⁻ 2 (q151 c4) ∷
   rw 3 (q152 c4) ∷
   rw 4 (q153 c4) ∷
   rw 5 (q152 c4) ∷
   rw⁻ 6 (q151 c4) ∷
   rw 7 (q153 c4) ∷
   rw 8 (q150 c4) ∷
   rw⁻ 9 (q149 c4) ∷
   re 11 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   rw⁻ 10 (q151 c4) ∷
   rw 11 (q152 c4) ∷
   rw 12 (q153 c4) ∷
   rw 13 (q152 c4) ∷
   rw⁻ 14 (q151 c4) ∷
   rw 15 (q153 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (Bx4-012 ∷ []) ∷
   re 5 6 (Bx4-012 ∷ []) ∷
   re 0 6 (Bx0-4312 ∷ []) ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = eqn (Bx3-1024 ∷ []) (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4)

-- box-perm-2134 @032032: 1 steps
lem-box-perm-2134-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-2134-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-0124 ∷ [])
  (rw 0 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = eqn (Sw13 ∷ Toff203 ∷ []) (Toff201 ∷ Sw13 ∷ []) (wl 286 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (Sw13 ∷ Toff012 ∷ []) (Toff023 ∷ Sw13 ∷ []) (wl 284 (lit c4))

-- nat-SWbc @02102331: 23 steps
lem-nat-SWbc-at02102331 : Ws → ⟪ (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-nat-SWbc-at02102331 c4 = derive (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) (Bx2-0134 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) ∷
   rw⁻ 0 (q138 c4) ∷
   rw 1 (q155 c4) ∷
   re 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 2 (q136 c4) ∷
   rw 3 (q156 c4) ∷
   rw 4 (q140 c4) ∷
   rw 5 (q156 c4) ∷
   rw⁻ 6 (q136 c4) ∷
   rw 7 (q140 c4) ∷
   rw 8 (q155 c4) ∷
   rw⁻ 9 (q138 c4) ∷
   re 11 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 10 (q136 c4) ∷
   rw 11 (q156 c4) ∷
   rw 12 (q140 c4) ∷
   rw 13 (q156 c4) ∷
   rw⁻ 14 (q136 c4) ∷
   rw 15 (q140 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (Bx0-234 ∷ []) ∷
   re 5 6 (Bx0-234 ∷ []) ∷
   re 0 6 (Bx2-0134 ∷ []) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4)

-- box-perm-2134 @0210243143: 1 steps
lem-box-perm-2134-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-2134-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-4013 ∷ [])
  (rw 0 (q157 c4) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp 450 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) (wl 1220 (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ134 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ134 ∷ []) (wp 1206 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp 1003 c4)

-- cQ @04122041: 7 steps
lem-cQ-at04122041 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at04122041 c4 = derive (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  (rw 0 (q158 c4) ∷
   rw⁻ 4 (q159 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 2 (q160 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q161 c4) ∷
   rw⁻ 1 (q158 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = eqn (CCZ234 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ024 ∷ []) (wp 1155 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (Sw03 ∷ Toff402 ∷ []) (Toff423 ∷ Sw03 ∷ []) (wp 1181 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (CCZ024 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ234 ∷ []) (wp 1157 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (Sw03 ∷ Toff234 ∷ []) (Toff204 ∷ Sw03 ∷ []) (wp 1180 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (Sw03 ∷ Bx4-21 ∷ []) (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (Sw03 ∷ Sw03 ∷ []) [] (wl 928 (lit c4))

-- nat-SWbc @04122041: 23 steps
lem-nat-SWbc-at04122041 : Ws → ⟪ (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-nat-SWbc-at04122041 c4 = derive (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) (Bx4-2301 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) ∷
   rw⁻ 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   re 3 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   rw⁻ 2 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q166 c4) ∷
   rw 5 (q165 c4) ∷
   rw⁻ 6 (q164 c4) ∷
   rw 7 (q166 c4) ∷
   rw 8 (q163 c4) ∷
   rw⁻ 9 (q162 c4) ∷
   re 11 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   rw⁻ 10 (q164 c4) ∷
   rw 11 (q165 c4) ∷
   rw 12 (q166 c4) ∷
   rw 13 (q165 c4) ∷
   rw⁻ 14 (q164 c4) ∷
   rw 15 (q166 c4) ∷
   rw 16 (q167 c4) ∷
   re 2 6 (Bx2-401 ∷ []) ∷
   re 5 6 (Bx2-401 ∷ []) ∷
   re 0 6 (Bx4-2301 ∷ []) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl 274 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) (wp 63 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)

-- cQ @0412233041: 7 steps
lem-cQ-at0412233041 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0412233041 c4 = derive (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  (rw 0 (q168 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 3 (q170 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 1 (q170 c4) ∷
   rw⁻ 0 (q172 c4) ∷
   rw⁻ 1 (q168 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ024 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ014 ∷ []) (wp 551 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (wp 973 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (CCZ014 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ024 ∷ []) (wp 553 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (wp 972 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4))

-- nat-SWbc @0410213243: 23 steps
lem-nat-SWbc-at0410213243 : Ws → ⟪ (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-nat-SWbc-at0410213243 c4 = derive (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (Bx4-0213 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) ∷
   rw⁻ 0 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   re 3 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   rw⁻ 2 (q175 c4) ∷
   rw 3 (q176 c4) ∷
   rw 4 (q177 c4) ∷
   rw 5 (q176 c4) ∷
   rw⁻ 6 (q175 c4) ∷
   rw 7 (q177 c4) ∷
   rw 8 (q174 c4) ∷
   rw⁻ 9 (q173 c4) ∷
   re 11 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   rw⁻ 10 (q175 c4) ∷
   rw 11 (q176 c4) ∷
   rw 12 (q177 c4) ∷
   rw 13 (q176 c4) ∷
   rw⁻ 14 (q175 c4) ∷
   rw 15 (q177 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (Bx0-413 ∷ []) ∷
   re 5 6 (Bx0-413 ∷ []) ∷
   re 0 6 (Bx4-0213 ∷ []) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp 296 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ []) (wl 1221 (lit c4))

-- cQ @04103143: 7 steps
lem-cQ-at04103143 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at04103143 c4 = derive (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  (rw 0 (q178 c4) ∷
   rw⁻ 4 (q161 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q178 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl 166 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)

-- cQ @04233042: 7 steps
lem-cQ-at04233042 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at04233042 c4 = derive (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  (rw 0 (q180 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 3 (q182 c4) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 1 (q182 c4) ∷
   rw⁻ 0 (q184 c4) ∷
   rw⁻ 1 (q180 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = eqn (Sw03 ∷ Toff423 ∷ []) (Toff402 ∷ Sw03 ∷ []) (wp 1158 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (Sw03 ∷ Toff204 ∷ []) (Toff234 ∷ Sw03 ∷ []) (wp 1156 c4)

-- nat-SWbc @0412233041: 23 steps
lem-nat-SWbc-at0412233041 : Ws → ⟪ (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-nat-SWbc-at0412233041 c4 = derive (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) (Bx4-2031 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-401 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ []) ∷
   rw⁻ 0 (q164 c4) ∷
   rw 1 (q185 c4) ∷
   re 3 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) ∷
   rw⁻ 2 (q162 c4) ∷
   rw 3 (q186 c4) ∷
   rw 4 (q166 c4) ∷
   rw 5 (q186 c4) ∷
   rw⁻ 6 (q162 c4) ∷
   rw 7 (q166 c4) ∷
   rw 8 (q185 c4) ∷
   rw⁻ 9 (q164 c4) ∷
   re 11 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) ∷
   rw⁻ 10 (q162 c4) ∷
   rw 11 (q186 c4) ∷
   rw 12 (q166 c4) ∷
   rw 13 (q186 c4) ∷
   rw⁻ 14 (q162 c4) ∷
   rw 15 (q166 c4) ∷
   rw 16 (q167 c4) ∷
   re 2 6 (Bx2-431 ∷ []) ∷
   re 5 6 (Bx2-431 ∷ []) ∷
   re 0 6 (Bx4-2031 ∷ []) ∷ []) Eq.refl

-- cQ @041041: 7 steps
lem-cQ-at041041 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at041041 c4 = derive (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  (rw 0 (q178 c4) ∷
   rw⁻ 4 (q161 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q178 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = eqn (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp 231 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (CCZ124 ∷ CS04 ∷ []) (CS04 ∷ CCZ124 ∷ []) (wp 384 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (CCZ124 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ124 ∷ []) (wl 1399 (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (CCZ124 ∷ CS34 ∷ []) (CS34 ∷ CCZ124 ∷ []) (wl 471 (lit c4))

-- cQ @0410233241: 7 steps
lem-cQ-at0410233241 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0410233241 c4 = derive (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  (rw 0 (q187 c4) ∷
   rw⁻ 4 (q188 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 2 (q189 c4) ∷
   rw 1 (q143 c4) ∷
   rw⁻ 0 (q190 c4) ∷
   rw⁻ 1 (q187 c4) ∷ []) Eq.refl

private
  q191 : Ws → Eqn
  q191 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl 271 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp 108 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CCZ034 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ034 ∷ []) (wp 123 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) (wp 106 c4)

-- cQ @0412213043: 7 steps
lem-cQ-at0412213043 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0412213043 c4 = derive (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  (rw 0 (q191 c4) ∷
   rw⁻ 4 (q192 c4) ∷
   rw 3 (q128 c4) ∷
   rw⁻ 2 (q193 c4) ∷
   rw 1 (q128 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q191 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl 831 (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ []) (wp 746 c4)

-- cQ @0413213240: 7 steps
lem-cQ-at0413213240 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0413213240 c4 = derive (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  (rw 0 (q195 c4) ∷
   rw⁻ 4 (q184 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 2 (q196 c4) ∷
   rw 1 (q109 c4) ∷
   rw⁻ 0 (q181 c4) ∷
   rw⁻ 1 (q195 c4) ∷ []) Eq.refl

-- cQ @04233240: 7 steps
lem-cQ-at04233240 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at04233240 c4 = derive (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  (rw 0 (q180 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 3 (q182 c4) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 1 (q182 c4) ∷
   rw⁻ 0 (q184 c4) ∷
   rw⁻ 1 (q180 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl 256 (lit c4))
  q198 : Ws → Eqn
  q198 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ []) (wp 107 c4)

-- cQ @0440: 7 steps
lem-cQ-at0440 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0440 c4 = derive (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  (rw 0 (q197 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 3 (q198 c4) ∷
   rw⁻ 2 (q199 c4) ∷
   rw 1 (q198 c4) ∷
   rw⁻ 0 (q192 c4) ∷
   rw⁻ 1 (q197 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = eqn (CCZ034 ∷ []) (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp 1193 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (CCZ124 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ124 ∷ []) (wp 318 c4)

-- cQ @0413203142: 7 steps
lem-cQ-at0413203142 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0413203142 c4 = derive (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  (rw 0 (q200 c4) ∷
   rw⁻ 4 (q190 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 2 (q201 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q188 c4) ∷
   rw⁻ 1 (q200 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl 334 (lit c4))
  q203 : Ws → Eqn
  q203 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp 513 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (CCZ023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ023 ∷ []) (wl 620 (lit c4))
  q205 : Ws → Eqn
  q205 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl 621 (lit c4))

-- cQ @02142140: 7 steps
lem-cQ-at02142140 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at02142140 c4 = derive (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  (rw 0 (q202 c4) ∷
   rw⁻ 4 (q203 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q202 c4) ∷ []) Eq.refl

-- cQ @0413213042: 7 steps
lem-cQ-at0413213042 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0413213042 c4 = derive (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  (rw 0 (q195 c4) ∷
   rw⁻ 4 (q184 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 2 (q196 c4) ∷
   rw 1 (q109 c4) ∷
   rw⁻ 0 (q181 c4) ∷
   rw⁻ 1 (q195 c4) ∷ []) Eq.refl

-- cQ @0412233140: 7 steps
lem-cQ-at0412233140 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0412233140 c4 = derive (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  (rw 0 (q168 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 3 (q170 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 1 (q170 c4) ∷
   rw⁻ 0 (q172 c4) ∷
   rw⁻ 1 (q168 c4) ∷ []) Eq.refl

private
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ124 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ234 ∷ []) (wl 1669 (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (Sw13 ∷ Toff423 ∷ []) (Toff412 ∷ Sw13 ∷ []) (wl 1670 (lit c4))
  q208 : Ws → Eqn
  q208 c4 = eqn (CCZ234 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ124 ∷ []) (wl 1671 (lit c4))
  q209 : Ws → Eqn
  q209 c4 = eqn (Sw13 ∷ Toff214 ∷ []) (Toff234 ∷ Sw13 ∷ []) (wl 1672 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (Sw13 ∷ Bx4-20 ∷ []) (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4))

-- nat-SWbc @0412233140: 23 steps
lem-nat-SWbc-at0412233140 : Ws → ⟪ (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-nat-SWbc-at0412233140 c4 = derive (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) (Bx4-2130 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) ∷
   rw⁻ 0 (q206 c4) ∷
   rw 1 (q207 c4) ∷
   re 3 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) ∷
   rw⁻ 2 (q208 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q210 c4) ∷
   rw 5 (q209 c4) ∷
   rw⁻ 6 (q208 c4) ∷
   rw 7 (q210 c4) ∷
   rw 8 (q207 c4) ∷
   rw⁻ 9 (q206 c4) ∷
   re 11 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) ∷
   rw⁻ 10 (q208 c4) ∷
   rw 11 (q209 c4) ∷
   rw 12 (q210 c4) ∷
   rw 13 (q209 c4) ∷
   rw⁻ 14 (q208 c4) ∷
   rw 15 (q210 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (Bx2-430 ∷ []) ∷
   re 5 6 (Bx2-430 ∷ []) ∷
   re 0 6 (Bx4-2130 ∷ []) ∷ []) Eq.refl

-- cQ @0410233142: 7 steps
lem-cQ-at0410233142 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0410233142 c4 = derive (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  (rw 0 (q187 c4) ∷
   rw⁻ 4 (q188 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 2 (q189 c4) ∷
   rw 1 (q143 c4) ∷
   rw⁻ 0 (q190 c4) ∷
   rw⁻ 1 (q187 c4) ∷ []) Eq.refl

-- cQ @04122140: 7 steps
lem-cQ-at04122140 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at04122140 c4 = derive (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  (rw 0 (q191 c4) ∷
   rw⁻ 4 (q192 c4) ∷
   rw 3 (q128 c4) ∷
   rw⁻ 2 (q193 c4) ∷
   rw 1 (q128 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q191 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = eqn (Sw13 ∷ Toff412 ∷ []) (Toff423 ∷ Sw13 ∷ []) (wl 1680 (lit c4))
  q212 : Ws → Eqn
  q212 c4 = eqn (Sw13 ∷ Toff234 ∷ []) (Toff214 ∷ Sw13 ∷ []) (wl 1681 (lit c4))

-- nat-SWbc @04122140: 23 steps
lem-nat-SWbc-at04122140 : Ws → ⟪ (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-nat-SWbc-at04122140 c4 = derive (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) (Bx4-2310 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) ∷
   rw⁻ 0 (q208 c4) ∷
   rw 1 (q211 c4) ∷
   re 3 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   rw⁻ 2 (q206 c4) ∷
   rw 3 (q212 c4) ∷
   rw 4 (q210 c4) ∷
   rw 5 (q212 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 7 (q210 c4) ∷
   rw 8 (q211 c4) ∷
   rw⁻ 9 (q208 c4) ∷
   re 11 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   rw⁻ 10 (q206 c4) ∷
   rw 11 (q212 c4) ∷
   rw 12 (q210 c4) ∷
   rw 13 (q212 c4) ∷
   rw⁻ 14 (q206 c4) ∷
   rw 15 (q210 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (Bx2-410 ∷ []) ∷
   re 5 6 (Bx2-410 ∷ []) ∷
   re 0 6 (Bx4-2310 ∷ []) ∷ []) Eq.refl

-- cQ @0413203241: 7 steps
lem-cQ-at0413203241 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0413203241 c4 = derive (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  (rw 0 (q200 c4) ∷
   rw⁻ 4 (q190 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 2 (q201 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q188 c4) ∷
   rw⁻ 1 (q200 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl 829 (lit c4))
  q214 : Ws → Eqn
  q214 c4 = eqn (CX32 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4))
  q215 : Ws → Eqn
  q215 c4 = eqn (CCZ014 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ014 ∷ []) (wp 722 c4)

-- cQ @04133140: 7 steps
lem-cQ-at04133140 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at04133140 c4 = derive (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  (rw 0 (q213 c4) ∷
   rw⁻ 4 (q172 c4) ∷
   rw 3 (q214 c4) ∷
   rw⁻ 2 (q215 c4) ∷
   rw 1 (q214 c4) ∷
   rw⁻ 0 (q169 c4) ∷
   rw⁻ 1 (q213 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = eqn (Sw12 ∷ Bx4-30 ∷ []) (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4))

-- nat-SWbc @04133140: 23 steps
lem-nat-SWbc-at04133140 : Ws → ⟪ (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-nat-SWbc-at04133140 c4 = derive (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) (Bx4-3120 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) ∷
   rw⁻ 0 (q18 c4) ∷
   rw 1 (q33 c4) ∷
   re 3 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q216 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 7 (q216 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   re 11 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) ∷
   rw⁻ 10 (q20 c4) ∷
   rw 11 (q32 c4) ∷
   rw 12 (q216 c4) ∷
   rw 13 (q32 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw 15 (q216 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (Bx3-420 ∷ []) ∷
   re 5 6 (Bx3-420 ∷ []) ∷
   re 0 6 (Bx4-3120 ∷ []) ∷ []) Eq.refl

-- nat-SWbc @0413213240: 23 steps
lem-nat-SWbc-at0413213240 : Ws → ⟪ (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413213240 c4 = derive (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) (Bx4-3210 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) ∷
   rw⁻ 0 (q20 c4) ∷
   rw 1 (q21 c4) ∷
   re 3 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) ∷
   rw⁻ 2 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q216 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw 7 (q216 c4) ∷
   rw 8 (q21 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   re 11 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 11 (q19 c4) ∷
   rw 12 (q216 c4) ∷
   rw 13 (q19 c4) ∷
   rw⁻ 14 (q18 c4) ∷
   rw 15 (q216 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (Bx3-410 ∷ []) ∷
   re 5 6 (Bx3-410 ∷ []) ∷
   re 0 6 (Bx4-3210 ∷ []) ∷ []) Eq.refl
