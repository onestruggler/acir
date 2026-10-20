{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D069 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0234 ; wl0241 ; wl0242 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0256 ; wl0305 ; wl0770 ; wl0872 ; wl1037 ; wl1294 ; wl1295 ; wl1296 ; wp0034 ; wp0035 ; wp0036 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0091 ; wp0092 ; wp0094 ; wp0095 ; wp0097 ; wp0617 ; wp0647 ; wp0785 ; wp0827 ; wp0842 ; wp0843 ; wp0845)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box2-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-S2-SBOX⟨0·1·42·3⟩ ; lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-CKc-box-at13213442 ; lem-box-perm-3421-at122441 ; lem-box-perm-4312-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D041 using (lem-nf-rel-268at1)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl0241 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp0089 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp0036 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp0034 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) (wp0097 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) (wp0095 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ234 ∷ []) (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (wp0842 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp0081 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx0-2431 ∷ []) (Bx0-3142 ∷ []) (lem-box-perm-3421-at122441 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Bx0-3142 ∷ CK42 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) (lem-CKc-box-at13213442 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (Bx0-3142 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-4312-at13213442 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff013 ∷ CS24 ∷ []) (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) (wp0785 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (S4 ∷ Toff013 ∷ []) (Toff013 ∷ S4 ∷ []) (wp0647 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ []) (wp0617 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp0092 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx0-2431 ∷ Bx0-2431 ∷ []) [] (lem-box2-at122441 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl0305 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ []) (CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ []) (wl1294 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0181 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) (S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl1295 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) (wl1296 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) (lem-nf-rel-268at1 c4)

-- F1-rel-268@1: 475 steps
lem-F1-rel-268at1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268at1 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ [])
  (rw 2 (q1 c4) ∷
   rw 5 (q2 c4) ∷
   rw 8 (q1 c4) ∷
   re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   re 10 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 12 1 (CS12 ∷ []) ∷
   re 14 1 (CS12⁻ ∷ []) ∷
   rw 10 (q3 c4) ∷
   rw 13 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw 14 (q6 c4) ∷
   rw 11 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q16 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 13 (q4 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw⁻ 12 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q9 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q12 c4) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 12 (q3 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 15 (q21 c4) ∷
   rw 14 (q22 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw 12 (q22 c4) ∷
   rw⁻ 13 (q3 c4) ∷
   rw 13 (q3 c4) ∷
   rw 16 (q4 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 17 (q6 c4) ∷
   rw 14 (q13 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw 16 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 15 (q14 c4) ∷
   rw 16 (q4 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw 13 (q20 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q11 c4) ∷
   rw 20 (q12 c4) ∷
   rw 14 (q6 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw 15 (q3 c4) ∷
   rw⁻ 18 (q23 c4) ∷
   rw 17 (q24 c4) ∷
   rw⁻ 16 (q23 c4) ∷
   rw 15 (q24 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 16 (q25 c4) ∷
   rw 16 (q26 c4) ∷
   rw 19 (q27 c4) ∷
   rw 19 (q3 c4) ∷
   rw 23 (q28 c4) ∷
   rw 22 (q29 c4) ∷
   rw⁻ 23 (q30 c4) ∷
   rw 24 (q31 c4) ∷
   rw⁻ 25 (q30 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw⁻ 22 (q28 c4) ∷
   rw 21 (q33 c4) ∷
   rw 21 (q28 c4) ∷
   rw 20 (q29 c4) ∷
   rw⁻ 21 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw⁻ 23 (q30 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw⁻ 20 (q28 c4) ∷
   rw 19 (q33 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw 20 (q25 c4) ∷
   rw 20 (q26 c4) ∷
   rw 23 (q27 c4) ∷
   rw 23 (q3 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw 25 (q35 c4) ∷
   rw⁻ 24 (q34 c4) ∷
   rw 23 (q35 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw 0 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q11 c4) ∷
   rw 10 (q12 c4) ∷
   rw 4 (q6 c4) ∷
   rw 1 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q12 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 4 (q22 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 3 (q3 c4) ∷
   rw 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q12 c4) ∷
   rw 7 (q6 c4) ∷
   rw 4 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q11 c4) ∷
   rw 10 (q12 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw 7 (q24 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 5 (q24 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw 6 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw 9 (q27 c4) ∷
   rw 9 (q3 c4) ∷
   rw 13 (q28 c4) ∷
   rw 12 (q29 c4) ∷
   rw⁻ 13 (q30 c4) ∷
   rw 14 (q31 c4) ∷
   rw⁻ 15 (q30 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw⁻ 12 (q28 c4) ∷
   rw 11 (q33 c4) ∷
   rw 11 (q28 c4) ∷
   rw 10 (q29 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw⁻ 13 (q30 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw 9 (q33 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   rw 10 (q25 c4) ∷
   rw 10 (q26 c4) ∷
   rw 13 (q27 c4) ∷
   rw 13 (q3 c4) ∷
   rw⁻ 16 (q34 c4) ∷
   rw 15 (q35 c4) ∷
   rw⁻ 14 (q34 c4) ∷
   rw 13 (q35 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw 14 (q3 c4) ∷
   rw 18 (q14 c4) ∷
   rw⁻ 17 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw 20 (q16 c4) ∷
   rw⁻ 21 (q18 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw 16 (q20 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw 16 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw⁻ 15 (q14 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 15 (q3 c4) ∷
   rw 15 (q3 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw 17 (q20 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 16 (q14 c4) ∷
   rw 15 (q20 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw 16 (q3 c4) ∷
   rw 19 (q4 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 21 (q6 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q9 c4) ∷
   rw 25 (q11 c4) ∷
   rw 26 (q12 c4) ∷
   rw 20 (q6 c4) ∷
   rw 17 (q13 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 22 (q18 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw 19 (q4 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 16 (q20 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q12 c4) ∷
   rw 17 (q6 c4) ∷
   rw⁻ 18 (q3 c4) ∷
   rw 18 (q3 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw 20 (q22 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 19 (q3 c4) ∷
   rw 19 (q3 c4) ∷
   rw 23 (q14 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw 21 (q20 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 20 (q14 c4) ∷
   rw 19 (q20 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw 20 (q3 c4) ∷
   rw 23 (q4 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 25 (q6 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q8 c4) ∷
   rw 26 (q9 c4) ∷
   rw 27 (q10 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q11 c4) ∷
   rw 30 (q12 c4) ∷
   rw 24 (q6 c4) ∷
   rw 21 (q13 c4) ∷
   rw 23 (q14 c4) ∷
   rw⁻ 22 (q15 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 26 (q18 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw 23 (q4 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw 20 (q20 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q8 c4) ∷
   rw 23 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q9 c4) ∷
   rw 26 (q11 c4) ∷
   rw 27 (q12 c4) ∷
   rw 21 (q6 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw 22 (q3 c4) ∷
   rw⁻ 25 (q23 c4) ∷
   rw 24 (q24 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw 22 (q24 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw 23 (q3 c4) ∷
   rw⁻ 26 (q36 c4) ∷
   rw 26 (q37 c4) ∷
   rw 25 (q38 c4) ∷
   rw 26 (q9 c4) ∷
   rw 27 (q39 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q22 c4) ∷
   rw⁻ 25 (q37 c4) ∷
   rw⁻ 24 (q36 c4) ∷
   rw 24 (q37 c4) ∷
   rw 23 (q38 c4) ∷
   rw 24 (q9 c4) ∷
   rw 25 (q39 c4) ∷
   rw 26 (q9 c4) ∷
   rw 27 (q22 c4) ∷
   rw⁻ 23 (q37 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw 24 (q25 c4) ∷
   rw 24 (q26 c4) ∷
   rw 27 (q27 c4) ∷
   rw 27 (q3 c4) ∷
   rw⁻ 30 (q36 c4) ∷
   rw 30 (q37 c4) ∷
   rw 29 (q38 c4) ∷
   rw 30 (q9 c4) ∷
   rw 31 (q39 c4) ∷
   rw 32 (q9 c4) ∷
   rw 33 (q22 c4) ∷
   rw⁻ 29 (q37 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw 28 (q37 c4) ∷
   rw 27 (q38 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q39 c4) ∷
   rw 30 (q9 c4) ∷
   rw 31 (q22 c4) ∷
   rw⁻ 27 (q37 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw 28 (q3 c4) ∷
   rw 32 (q28 c4) ∷
   rw 31 (q29 c4) ∷
   rw⁻ 32 (q30 c4) ∷
   rw 33 (q31 c4) ∷
   rw⁻ 34 (q30 c4) ∷
   rw⁻ 35 (q32 c4) ∷
   rw⁻ 31 (q28 c4) ∷
   rw 30 (q33 c4) ∷
   rw 30 (q28 c4) ∷
   rw 29 (q29 c4) ∷
   rw⁻ 30 (q30 c4) ∷
   rw 31 (q31 c4) ∷
   rw⁻ 32 (q30 c4) ∷
   rw⁻ 33 (q32 c4) ∷
   rw⁻ 29 (q28 c4) ∷
   rw 28 (q33 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw 29 (q3 c4) ∷
   rw⁻ 32 (q36 c4) ∷
   rw 32 (q37 c4) ∷
   rw 31 (q38 c4) ∷
   rw 32 (q9 c4) ∷
   rw 33 (q39 c4) ∷
   rw 34 (q9 c4) ∷
   rw 35 (q22 c4) ∷
   rw⁻ 31 (q37 c4) ∷
   rw⁻ 30 (q36 c4) ∷
   rw 30 (q37 c4) ∷
   rw 29 (q38 c4) ∷
   rw 30 (q9 c4) ∷
   rw 31 (q39 c4) ∷
   rw 32 (q9 c4) ∷
   rw 33 (q22 c4) ∷
   rw⁻ 29 (q37 c4) ∷
   rw⁻ 30 (q3 c4) ∷
   rw 30 (q25 c4) ∷
   rw 30 (q26 c4) ∷
   rw 33 (q27 c4) ∷
   rw 33 (q3 c4) ∷
   rw⁻ 36 (q36 c4) ∷
   rw 36 (q37 c4) ∷
   rw 35 (q38 c4) ∷
   rw 36 (q9 c4) ∷
   rw 37 (q39 c4) ∷
   rw 38 (q9 c4) ∷
   rw 39 (q22 c4) ∷
   rw⁻ 35 (q37 c4) ∷
   rw⁻ 34 (q36 c4) ∷
   rw 34 (q37 c4) ∷
   rw 33 (q38 c4) ∷
   rw 34 (q9 c4) ∷
   rw 35 (q39 c4) ∷
   rw 36 (q9 c4) ∷
   rw 37 (q22 c4) ∷
   rw⁻ 33 (q37 c4) ∷
   rw⁻ 34 (q3 c4) ∷
   rw 34 (q3 c4) ∷
   rw⁻ 37 (q34 c4) ∷
   rw 36 (q35 c4) ∷
   rw⁻ 35 (q34 c4) ∷
   rw 34 (q35 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw 35 (q40 c4) ∷
   rw 0 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 4 (q43 c4) ∷
   rw 29 (q44 c4) ∷
   rw 5 (q45 c4) ∷
   rw 6 (q44 c4) ∷
   rw 7 (q46 c4) ∷
   rw 17 (q44 c4) ∷
   rw 8 (q42 c4) ∷
   rw 8 (q41 c4) ∷
   rw 10 (q42 c4) ∷
   rw 15 (q44 c4) ∷
   rw 16 (q44 c4) ∷
   rw 0 (q47 c4) ∷
   rw⁻ 0 (q48 c4) ∷ []) Eq.refl
