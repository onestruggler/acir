{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0006 ; wl0018 ; wl0518 ; wl0788 ; wp0135 ; wp0153 ; wp0154 ; wl0288 ; wl0293 ; wl0294 ; wl0415 ; wl0928 ; wl0929 ; wp0130 ; wp0140 ; wp0141 ; wp0162 ; wp0279 ; wp0280 ; wp0765 ; wp0766 ; wp0767 ; wl0004 ; wl0205 ; wp0131 ; wp0216 ; wp0527 ; wp0529 ; wp0812 ; wp0813 ; wl0184 ; wl1044 ; wl1045 ; wl1046 ; wl1047 ; wl1048 ; wl1049 ; wp0847 ; wp0848 ; wl0432 ; wl0433 ; wl1052 ; wl1053 ; wl1054 ; wl1055 ; wl1057 ; wl1058 ; wl1059 ; wl1060 ; wl1061 ; wl1063 ; wl1064 ; wl1067 ; wl1077 ; wl1078 ; wl1079 ; wl1080 ; wl1102 ; wl1103 ; wl1104 ; wl1105 ; wl1106 ; wl1107 ; wl1108 ; wl1109 ; wl1110 ; wl1111 ; wp0019 ; wp0294 ; wp0850 ; wp0851 ; wp0852 ; wp0853 ; wp0854 ; wp0855 ; wp0861 ; wp0862 ; wp0865 ; wp0867 ; wp0868 ; wp0869 ; wp0902 ; wp0903 ; wp0904 ; wl1122 ; wl1123 ; wl1124 ; wl1125 ; wl1126 ; wl1137 ; wl1138 ; wl0231 ; wl1155 ; wp0214 ; wp0528 ; wp0530 ; wp0398 ; wp0551 ; wp0553 ; wp0957 ; wp0958 ; wp0959 ; wp0965 ; wp0966 ; wp0972 ; wp0973 ; wp0992 ; wl0322 ; wl1210 ; wl1211 ; wl1212 ; wl1216 ; wl1217 ; wl1218 ; wl1219 ; wl1231 ; wl1232 ; wp1014 ; wp1015 ; wp1016 ; wp0175 ; wp0176 ; wp0177 ; wp0178 ; wp0273 ; wp0274 ; wl1303 ; wp0262 ; wl0330 ; wl0331 ; wl1319 ; wl0030 ; wl0031 ; wl0063 ; wl0135 ; wl0136 ; wl1340 ; wp0111 ; wp0008)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) (wp0154 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ []) (wp0153 c4)

-- sym-ab @1331: 18 steps
lem-sym-ab-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym-ab-at1331 c4 = derive (Bx0-3214 ∷ []) (Bx0-2314 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (Bx0-24 ∷ []) ∷
   re 7 1 (Bx0-24 ∷ []) ∷
   re 2 6 (Bx2-014 ∷ []) ∷
   re 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Bx0-24 ∷ []) ∷
   re 10 1 (Bx0-24 ∷ []) ∷
   re 5 6 (Bx2-014 ∷ []) ∷
   re 0 6 (Bx0-2314 ∷ []) ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) (wl0518 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ []) (wp0280 c4)

-- sym-ab @0220: 18 steps
lem-sym-ab-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym-ab-at0220 c4 = derive (Bx2-1034 ∷ []) (Bx2-0134 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   re 4 1 (Bx2-04 ∷ []) ∷
   re 7 1 (Bx2-04 ∷ []) ∷
   re 2 6 (Bx0-234 ∷ []) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (Bx2-04 ∷ []) ∷
   re 10 1 (Bx2-04 ∷ []) ∷
   re 5 6 (Bx0-234 ∷ []) ∷
   re 0 6 (Bx2-0134 ∷ []) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4))

-- sym-ab @14233241: 18 steps
lem-sym-ab-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym-ab-at14233241 c4 = derive (Bx0-4321 ∷ []) (Bx0-3421 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   re 4 1 (Bx0-31 ∷ []) ∷
   re 7 1 (Bx0-31 ∷ []) ∷
   re 2 6 (Bx3-021 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   re 7 1 (Bx0-31 ∷ []) ∷
   re 10 1 (Bx0-31 ∷ []) ∷
   re 5 6 (Bx3-021 ∷ []) ∷
   re 0 6 (Bx0-3421 ∷ []) ∷ []) Eq.refl

-- sym-ab @021021: 18 steps
lem-sym-ab-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym-ab-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-1034 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (Bx2-14 ∷ []) ∷
   re 7 1 (Bx2-14 ∷ []) ∷
   re 2 6 (Bx1-234 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Bx2-14 ∷ []) ∷
   re 10 1 (Bx2-14 ∷ []) ∷
   re 5 6 (Bx1-234 ∷ []) ∷
   re 0 6 (Bx2-1034 ∷ []) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ234 ∷ CS02 ∷ []) (CS02 ∷ CCZ234 ∷ []) (wp0279 c4)

-- cQ @0220: 7 steps
lem-cQ-at0220 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0220 c4 = derive (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  (rw 0 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q7 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ []) (wl0294 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ012 ∷ []) (wp0140 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ012 ∷ CS24 ∷ []) (CS24 ∷ CCZ012 ∷ []) (wp0141 c4)

-- cQ @0213243140: 7 steps
lem-cQ-at0213243140 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0213243140 c4 = derive (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  (rw 0 (q12 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q12 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ024 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4)

-- sym-ab @0213213440: 18 steps
lem-sym-ab-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym-ab-at0213213440 c4 = derive (Bx2-3140 ∷ []) (Bx2-1340 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   re 4 1 (Bx2-10 ∷ []) ∷
   re 7 1 (Bx2-10 ∷ []) ∷
   re 2 6 (Bx1-240 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   re 7 1 (Bx2-10 ∷ []) ∷
   re 10 1 (Bx2-10 ∷ []) ∷
   re 5 6 (Bx1-240 ∷ []) ∷
   re 0 6 (Bx2-1340 ∷ []) ∷ []) Eq.refl

-- sym-ab @02233440: 18 steps
lem-sym-ab-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym-ab-at02233440 c4 = derive (Bx2-1340 ∷ []) (Bx2-3140 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q18 c4) ∷
   rw 2 (q17 c4) ∷
   re 4 1 (Bx2-30 ∷ []) ∷
   re 7 1 (Bx2-30 ∷ []) ∷
   re 2 6 (Bx3-240 ∷ []) ∷
   re 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 5 (q17 c4) ∷
   re 7 1 (Bx2-30 ∷ []) ∷
   re 10 1 (Bx2-30 ∷ []) ∷
   re 5 6 (Bx3-240 ∷ []) ∷
   re 0 6 (Bx2-3140 ∷ []) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ []) (wp0529 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) (wp0812 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ023 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ024 ∷ []) (wp0527 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) (wp0813 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx0-21 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-21 ∷ []) (c₃ (CZ ↑) (Swap))
  q24 : Ws → Eqn
  q24 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 (lit c4))

-- nat-SWbc @12233441: 23 steps
lem-nat-SWbc-at12233441 : Ws → ⟪ (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-nat-SWbc-at12233441 c4 = derive (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (Bx0-2431 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 1 (q20 c4) ∷
   re 3 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   re 11 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   rw⁻ 10 (q21 c4) ∷
   rw 11 (q22 c4) ∷
   rw⁻ 12 (q23 c4) ∷
   rw 13 (q22 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (Bx2-031 ∷ []) ∷
   re 5 6 (Bx2-031 ∷ []) ∷
   re 0 6 (Bx0-2431 ∷ []) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ023 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (wp0216 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) (wl0205 (lit c4))

-- sym-ab @14213243: 18 steps
lem-sym-ab-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym-ab-at14213243 c4 = derive (Bx0-4123 ∷ []) (Bx0-1423 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw⁻ 2 (q25 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   re 4 1 (Bx0-13 ∷ []) ∷
   re 7 1 (Bx0-13 ∷ []) ∷
   re 2 6 (Bx1-023 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw⁻ 5 (q25 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (Bx0-13 ∷ []) ∷
   re 10 1 (Bx0-13 ∷ []) ∷
   re 5 6 (Bx1-023 ∷ []) ∷
   re 0 6 (Bx0-1423 ∷ []) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) (wp0131 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) (wp0130 c4)

-- sym-ab @132132: 18 steps
lem-sym-ab-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym-ab-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-1324 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   re 4 1 (CZ34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   rw 2 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   re 4 1 (Bx0-14 ∷ []) ∷
   re 7 1 (Bx0-14 ∷ []) ∷
   re 2 6 (Bx1-024 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   re 7 1 (CZ34 ∷ []) ∷
   re 10 1 (CZ34 ∷ []) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   re 7 1 (Bx0-14 ∷ []) ∷
   re 10 1 (Bx0-14 ∷ []) ∷
   re 5 6 (Bx1-024 ∷ []) ∷
   re 0 6 (Bx0-1324 ∷ []) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (CS04 ∷ S4 ∷ []) (S4 ∷ CS04 ∷ []) (wp0847 c4)

-- F2-I-S0: 1 steps
lem-F2-I-S0 : Ws → ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S0 c4 = derive (S4 ∷ CS04 ∷ []) (CS04 ∷ S4 ∷ [])
  (rw⁻ 0 (q29 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (CS14 ∷ S4 ∷ []) (S4 ∷ CS14 ∷ []) (wl1044 (lit c4))

-- F2-I-S1: 1 steps
lem-F2-I-S1 : Ws → ⟪ (S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S1 c4 = derive (S4 ∷ CS14 ∷ []) (CS14 ∷ S4 ∷ [])
  (rw⁻ 0 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = eqn (CS24 ∷ S4 ∷ []) (S4 ∷ CS24 ∷ []) (wl1045 (lit c4))

-- F2-I-S2: 1 steps
lem-F2-I-S2 : Ws → ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S2 c4 = derive (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ [])
  (rw⁻ 0 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (CS34 ∷ S4 ∷ []) (S4 ∷ CS34 ∷ []) (wl1046 (lit c4))

-- F2-I-S3: 1 steps
lem-F2-I-S3 : Ws → ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S3 c4 = derive (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ [])
  (rw⁻ 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (CK40 ∷ S4 ∷ []) (S4 ∷ CK40 ∷ []) (wp0848 c4)

-- F2-I-K0: 1 steps
lem-F2-I-K0 : Ws → ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K0 c4 = derive (S4 ∷ CK40 ∷ []) (CK40 ∷ S4 ∷ [])
  (rw⁻ 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (CK41 ∷ S4 ∷ []) (S4 ∷ CK41 ∷ []) (wl1047 (lit c4))

-- F2-I-K1: 1 steps
lem-F2-I-K1 : Ws → ⟪ (S4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K1 c4 = derive (S4 ∷ CK41 ∷ []) (CK41 ∷ S4 ∷ [])
  (rw⁻ 0 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = eqn (CK42 ∷ S4 ∷ []) (S4 ∷ CK42 ∷ []) (wl1048 (lit c4))

-- F2-I-K2: 1 steps
lem-F2-I-K2 : Ws → ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K2 c4 = derive (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ [])
  (rw⁻ 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (CK43 ∷ S4 ∷ []) (S4 ∷ CK43 ∷ []) (wl1049 (lit c4))

-- F2-I-K3: 1 steps
lem-F2-I-K3 : Ws → ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K3 c4 = derive (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ [])
  (rw⁻ 0 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = eqn (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ []) (wp0850 c4)

-- F2-S0-S1: 1 steps
lem-F2-S0-S1 : Ws → ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S1 c4 = derive (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ [])
  (rw 0 (q37 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = eqn (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ []) (wp0851 c4)

-- F2-S0-S2: 1 steps
lem-F2-S0-S2 : Ws → ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S2 c4 = derive (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ [])
  (rw 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ []) (wp0852 c4)

-- F2-S0-S3: 1 steps
lem-F2-S0-S3 : Ws → ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S3 c4 = derive (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ [])
  (rw 0 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (CK41 ∷ CS04 ∷ []) (CS04 ∷ CK41 ∷ []) (wp0853 c4)

-- F2-S0-K1: 1 steps
lem-F2-S0-K1 : Ws → ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K1 c4 = derive (CS04 ∷ CK41 ∷ []) (CK41 ∷ CS04 ∷ [])
  (rw⁻ 0 (q40 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = eqn (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ []) (wp0854 c4)

-- F2-S0-K2: 1 steps
lem-F2-S0-K2 : Ws → ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K2 c4 = derive (CS04 ∷ CK42 ∷ []) (CK42 ∷ CS04 ∷ [])
  (rw⁻ 0 (q41 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ []) (wp0855 c4)

-- F2-S0-K3: 1 steps
lem-F2-S0-K3 : Ws → ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K3 c4 = derive (CS04 ∷ CK43 ∷ []) (CK43 ∷ CS04 ∷ [])
  (rw⁻ 0 (q42 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = eqn (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ []) (wl1052 (lit c4))

-- F2-S1-S2: 1 steps
lem-F2-S1-S2 : Ws → ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-S2 c4 = derive (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ [])
  (rw 0 (q43 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ []) (wl1053 (lit c4))

-- F2-S1-S3: 1 steps
lem-F2-S1-S3 : Ws → ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-S3 c4 = derive (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ [])
  (rw 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (CK40 ∷ CS14 ∷ []) (CS14 ∷ CK40 ∷ []) (wp0861 c4)

-- F2-S1-K0: 1 steps
lem-F2-S1-K0 : Ws → ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K0 c4 = derive (CS14 ∷ CK40 ∷ []) (CK40 ∷ CS14 ∷ [])
  (rw⁻ 0 (q45 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ []) (wl1054 (lit c4))

-- F2-S1-K2: 1 steps
lem-F2-S1-K2 : Ws → ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K2 c4 = derive (CS14 ∷ CK42 ∷ []) (CK42 ∷ CS14 ∷ [])
  (rw⁻ 0 (q46 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = eqn (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ []) (wl1055 (lit c4))

-- F2-S1-K3: 1 steps
lem-F2-S1-K3 : Ws → ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K3 c4 = derive (CS14 ∷ CK43 ∷ []) (CK43 ∷ CS14 ∷ [])
  (rw⁻ 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = eqn (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ []) (wl1057 (lit c4))

-- F2-S2-S3: 1 steps
lem-F2-S2-S3 : Ws → ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-S3 c4 = derive (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ [])
  (rw 0 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (CK40 ∷ CS24 ∷ []) (CS24 ∷ CK40 ∷ []) (wp0862 c4)

-- F2-S2-K0: 1 steps
lem-F2-S2-K0 : Ws → ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K0 c4 = derive (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ [])
  (rw⁻ 0 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = eqn (CK41 ∷ CS24 ∷ []) (CS24 ∷ CK41 ∷ []) (wl1058 (lit c4))

-- F2-S2-K1: 1 steps
lem-F2-S2-K1 : Ws → ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K1 c4 = derive (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ [])
  (rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ []) (wl1059 (lit c4))

-- F2-S2-K3: 1 steps
lem-F2-S2-K3 : Ws → ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K3 c4 = derive (CS24 ∷ CK43 ∷ []) (CK43 ∷ CS24 ∷ [])
  (rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (CK40 ∷ CS34 ∷ []) (CS34 ∷ CK40 ∷ []) (wp0865 c4)

-- F2-S3-K0: 1 steps
lem-F2-S3-K0 : Ws → ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K0 c4 = derive (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ [])
  (rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = eqn (CK41 ∷ CS34 ∷ []) (CS34 ∷ CK41 ∷ []) (wl1060 (lit c4))

-- F2-S3-K1: 1 steps
lem-F2-S3-K1 : Ws → ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K1 c4 = derive (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ [])
  (rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = eqn (CK42 ∷ CS34 ∷ []) (CS34 ∷ CK42 ∷ []) (wl1061 (lit c4))

-- F2-S3-K2: 1 steps
lem-F2-S3-K2 : Ws → ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K2 c4 = derive (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ [])
  (rw⁻ 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ []) (wp0867 c4)

-- F2-K0-K1: 1 steps
lem-F2-K0-K1 : Ws → ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K1 c4 = derive (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ [])
  (rw 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = eqn (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ []) (wp0868 c4)

-- F2-K0-K2: 1 steps
lem-F2-K0-K2 : Ws → ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K2 c4 = derive (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ [])
  (rw 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ []) (wp0869 c4)

-- F2-K0-K3: 1 steps
lem-F2-K0-K3 : Ws → ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K3 c4 = derive (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ [])
  (rw 0 (q57 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = eqn (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ []) (wl1063 (lit c4))

-- F2-K1-K2: 1 steps
lem-F2-K1-K2 : Ws → ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-K2 c4 = derive (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ [])
  (rw 0 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = eqn (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ []) (wl1064 (lit c4))

-- F2-K1-K3: 1 steps
lem-F2-K1-K3 : Ws → ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-K3 c4 = derive (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ [])
  (rw 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = eqn (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ []) (wl1067 (lit c4))

-- F2-K2-K3: 1 steps
lem-F2-K2-K3 : Ws → ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2-K3 c4 = derive (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ [])
  (rw 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl1077 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0788 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl1078 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] (wl1079 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0135 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0019 c4)

-- inv-SBOX(2;0;41;3): 30 steps
lem-inv-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-inv-SBOX⟨2·0·41·3⟩ c4 = derive (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) []
  (re 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 4 1 (CS03⁻ ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   rw 4 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   re 2 1 (CS03 ∷ []) ∷
   re 3 1 (CS03⁻ ∷ []) ∷
   rw 2 (q63 c4) ∷
   rw 1 (q62 c4) ∷
   re 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 6 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   re 11 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 11 1 (CZ03 ∷ []) ∷
   re 14 1 (CZ03 ∷ []) ∷
   rw 5 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw 3 (q66 c4) ∷
   re 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 8 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 8 1 (CZ03 ∷ []) ∷
   re 11 1 (CZ03 ∷ []) ∷
   rw 2 (q64 c4) ∷
   rw 1 (q66 c4) ∷
   rw 0 (q65 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] (wl1080 (lit c4))

-- invr-SBOX(2;0;41;3): 30 steps
lem-invr-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-invr-SBOX⟨2·0·41·3⟩ c4 = derive (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) []
  (re 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 10 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw 9 (q65 c4) ∷
   rw 8 (q66 c4) ∷
   re 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   re 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 15 1 (CZ03 ∷ []) ∷
   re 18 1 (CZ03 ∷ []) ∷
   rw 7 (q67 c4) ∷
   rw 6 (q66 c4) ∷
   rw 5 (q65 c4) ∷
   re 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 12 1 (CZ03 ∷ []) ∷
   re 15 1 (CZ03 ∷ []) ∷
   rw 4 (q67 c4) ∷
   rw 3 (q62 c4) ∷
   re 2 1 (CS03⁻ ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw 2 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   re 0 1 (CS03 ∷ []) ∷
   re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q63 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = eqn (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) [] (wl1102 (lit c4))

-- F1-order-I@0: 1 steps
lem-F1-order-Iat0 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Iat0 c4 = derive (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  (rw 0 (q68 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) [] (wp0902 c4)

-- F1-order-S@0: 1 steps
lem-F1-order-Sat0 : Ws → ⟪ (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat0 c4 = derive (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) []
  (rw 0 (q69 c4) ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = eqn (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) [] (wl1103 (lit c4))

-- F1-order-S@1: 1 steps
lem-F1-order-Sat1 : Ws → ⟪ (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat1 c4 = derive (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) []
  (rw 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) [] (wl1104 (lit c4))

-- F1-order-S@2: 1 steps
lem-F1-order-Sat2 : Ws → ⟪ (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat2 c4 = derive (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) []
  (rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) [] (wl1105 (lit c4))

-- F1-order-S@3: 1 steps
lem-F1-order-Sat3 : Ws → ⟪ (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat3 c4 = derive (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) []
  (rw 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wp0903 c4)

-- F1-order-K@0: 1 steps
lem-F1-order-Kat0 : Ws → ⟪ (CK40 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat0 c4 = derive (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (CK41 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl1106 (lit c4))

-- F1-order-K@1: 1 steps
lem-F1-order-Kat1 : Ws → ⟪ (CK41 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat1 c4 = derive (CK41 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q74 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = eqn (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl1107 (lit c4))

-- F1-order-K@2: 1 steps
lem-F1-order-Kat2 : Ws → ⟪ (CK42 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat2 c4 = derive (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q75 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl1108 (lit c4))

-- F1-order-K@3: 1 steps
lem-F1-order-Kat3 : Ws → ⟪ (CK43 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat3 c4 = derive (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wp0904 c4)

-- F1-order-SK@0: 1 steps
lem-F1-order-SKat0 : Ws → ⟪ (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat0 c4 = derive (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = eqn (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl1109 (lit c4))

-- F1-order-SK@1: 1 steps
lem-F1-order-SKat1 : Ws → ⟪ (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat1 c4 = derive (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl1110 (lit c4))

-- F1-order-SK@2: 1 steps
lem-F1-order-SKat2 : Ws → ⟪ (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat2 c4 = derive (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) (wl1111 (lit c4))

-- F1-order-SK@3: 1 steps
lem-F1-order-SKat3 : Ws → ⟪ (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat3 c4 = derive (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  (rw 0 (q80 c4) ∷ []) Eq.refl

-- nf-order-CS@0: 0 steps
lem-nf-order-CSat0 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat0 c4 = refl

-- nf-order-CS@1: 0 steps
lem-nf-order-CSat1 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat1 c4 = refl

-- nf-order-CS@2: 0 steps
lem-nf-order-CSat2 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat2 c4 = refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ124 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ123 ∷ []) (wl1122 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (Sw34 ∷ Toff213 ∷ []) (Toff214 ∷ Sw34 ∷ []) (wl1123 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ123 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ124 ∷ []) (wl1124 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Sw34 ∷ Toff124 ∷ []) (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx2-10 ∷ Sw34 ∷ []) (Sw34 ∷ Bx2-10 ∷ []) (c₂ (CZ) (Swap ↑))

-- nat-SWbc @02233440: 23 steps
lem-nat-SWbc-at02233440 : Ws → ⟪ (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-nat-SWbc-at02233440 c4 = derive (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (Bx2-1430 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) ∷
   rw⁻ 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   re 3 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw 8 (q82 c4) ∷
   rw⁻ 9 (q81 c4) ∷
   re 11 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 10 (q83 c4) ∷
   rw 11 (q84 c4) ∷
   rw⁻ 12 (q85 c4) ∷
   rw 13 (q84 c4) ∷
   rw⁻ 14 (q83 c4) ∷
   rw⁻ 15 (q85 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (Bx1-230 ∷ []) ∷
   re 5 6 (Bx1-230 ∷ []) ∷
   re 0 6 (Bx2-1430 ∷ []) ∷ []) Eq.refl

private
  q86 : Ws → Eqn
  q86 c4 = eqn (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ []) (wl1137 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (Sw34 ∷ Toff123 ∷ []) (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4))

-- nat-SWbc @022440: 23 steps
lem-nat-SWbc-at022440 : Ws → ⟪ (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-nat-SWbc-at022440 c4 = derive (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (Bx2-1340 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) ∷
   rw⁻ 0 (q83 c4) ∷
   rw 1 (q86 c4) ∷
   re 3 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 2 (q81 c4) ∷
   rw 3 (q87 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw 8 (q86 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   re 11 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 10 (q81 c4) ∷
   rw 11 (q87 c4) ∷
   rw⁻ 12 (q85 c4) ∷
   rw 13 (q87 c4) ∷
   rw⁻ 14 (q81 c4) ∷
   rw⁻ 15 (q85 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (Bx1-240 ∷ []) ∷
   re 5 6 (Bx1-240 ∷ []) ∷
   re 0 6 (Bx2-1340 ∷ []) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ013 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp0214 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ013 ∷ []) (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4))

-- sym-ab @1441: 18 steps
lem-sym-ab-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym-ab-at1441 c4 = derive (Bx0-4231 ∷ []) (Bx0-2431 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   re 4 1 (Bx0-21 ∷ []) ∷
   re 7 1 (Bx0-21 ∷ []) ∷
   re 2 6 (Bx2-031 ∷ []) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q88 c4) ∷
   rw 5 (q89 c4) ∷
   re 7 1 (Bx0-21 ∷ []) ∷
   re 10 1 (Bx0-21 ∷ []) ∷
   re 5 6 (Bx2-031 ∷ []) ∷
   re 0 6 (Bx0-2431 ∷ []) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (wp0530 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) (wp0528 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Bx2-01 ∷ Sw34 ∷ []) (Sw34 ∷ Bx2-01 ∷ []) (c₂ (CZ) (Swap ↑))

-- nat-SWbc @0210233441: 23 steps
lem-nat-SWbc-at0210233441 : Ws → ⟪ (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210233441 c4 = derive (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (Bx2-0431 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) ∷
   rw⁻ 0 (q19 c4) ∷
   rw 1 (q90 c4) ∷
   re 3 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q91 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw 5 (q91 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 8 (q90 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   re 11 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   rw⁻ 10 (q21 c4) ∷
   rw 11 (q91 c4) ∷
   rw⁻ 12 (q92 c4) ∷
   rw 13 (q91 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw⁻ 15 (q92 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (Bx0-231 ∷ []) ∷
   re 5 6 (Bx0-231 ∷ []) ∷
   re 0 6 (Bx2-0431 ∷ []) ∷ []) Eq.refl

-- nat-SWbc @02102441: 23 steps
lem-nat-SWbc-at02102441 : Ws → ⟪ (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-nat-SWbc-at02102441 c4 = derive (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (Bx2-0341 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   re 3 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   re 11 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw⁻ 12 (q92 c4) ∷
   rw 13 (q20 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 15 (q92 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (Bx0-241 ∷ []) ∷
   re 5 6 (Bx0-241 ∷ []) ∷
   re 0 6 (Bx2-0341 ∷ []) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ014 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ013 ∷ []) (wp0398 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (wp0957 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ013 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ014 ∷ []) (wp0958 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ []) (wp0959 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx0-12 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-12 ∷ []) (c₃ (CZ ↑) (Swap))

-- nat-SWbc @233442: 23 steps
lem-nat-SWbc-at233442 : Ws → ⟪ (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-nat-SWbc-at233442 c4 = derive (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (Bx0-1432 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) ∷
   rw⁻ 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   re 3 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   rw⁻ 2 (q95 c4) ∷
   rw 3 (q96 c4) ∷
   rw⁻ 4 (q97 c4) ∷
   rw 5 (q96 c4) ∷
   rw⁻ 6 (q95 c4) ∷
   rw⁻ 7 (q97 c4) ∷
   rw 8 (q94 c4) ∷
   rw⁻ 9 (q93 c4) ∷
   re 11 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   rw⁻ 10 (q95 c4) ∷
   rw 11 (q96 c4) ∷
   rw⁻ 12 (q97 c4) ∷
   rw 13 (q96 c4) ∷
   rw⁻ 14 (q95 c4) ∷
   rw⁻ 15 (q97 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (Bx1-032 ∷ []) ∷
   re 5 6 (Bx1-032 ∷ []) ∷
   re 0 6 (Bx0-1432 ∷ []) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (wp0965 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ []) (wp0966 c4)

-- nat-SWbc @2442: 23 steps
lem-nat-SWbc-at2442 : Ws → ⟪ (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-nat-SWbc-at2442 c4 = derive (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (Bx0-1342 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   rw⁻ 0 (q95 c4) ∷
   rw 1 (q98 c4) ∷
   re 3 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q99 c4) ∷
   rw⁻ 4 (q97 c4) ∷
   rw 5 (q99 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   rw⁻ 7 (q97 c4) ∷
   rw 8 (q98 c4) ∷
   rw⁻ 9 (q95 c4) ∷
   re 11 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   rw⁻ 10 (q93 c4) ∷
   rw 11 (q99 c4) ∷
   rw⁻ 12 (q97 c4) ∷
   rw 13 (q99 c4) ∷
   rw⁻ 14 (q93 c4) ∷
   rw⁻ 15 (q97 c4) ∷
   rw 16 (q24 c4) ∷
   re 2 6 (Bx1-042 ∷ []) ∷
   re 5 6 (Bx1-042 ∷ []) ∷
   re 0 6 (Bx0-1342 ∷ []) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ014 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ024 ∷ []) (wp0553 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (wp0972 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ024 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ014 ∷ []) (wp0551 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (wp0973 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Sw12 ∷ Bx0-43 ∷ []) (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))
  q105 : Ws → Eqn
  q105 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0006 (lit c4))

-- nat-SWbc @143143: 23 steps
lem-nat-SWbc-at143143 : Ws → ⟪ (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-nat-SWbc-at143143 c4 = derive (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (Bx0-4123 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) ∷
   rw⁻ 0 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   re 3 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 3 (q103 c4) ∷
   rw 4 (q104 c4) ∷
   rw 5 (q103 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw 7 (q104 c4) ∷
   rw 8 (q101 c4) ∷
   rw⁻ 9 (q100 c4) ∷
   re 11 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   rw⁻ 10 (q102 c4) ∷
   rw 11 (q103 c4) ∷
   rw 12 (q104 c4) ∷
   rw 13 (q103 c4) ∷
   rw⁻ 14 (q102 c4) ∷
   rw 15 (q104 c4) ∷
   rw 16 (q105 c4) ∷
   re 2 6 (Bx4-023 ∷ []) ∷
   re 5 6 (Bx4-023 ∷ []) ∷
   re 0 6 (Bx0-4123 ∷ []) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ023 ∷ []) (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ023 ∷ []) (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4))

-- sym-ab @0314213240: 18 steps
lem-sym-ab-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym-ab-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Bx3-1420 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw⁻ 2 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   re 4 1 (Bx3-10 ∷ []) ∷
   re 7 1 (Bx3-10 ∷ []) ∷
   re 2 6 (Bx1-320 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw⁻ 5 (q106 c4) ∷
   rw 5 (q107 c4) ∷
   re 7 1 (Bx3-10 ∷ []) ∷
   re 10 1 (Bx3-10 ∷ []) ∷
   re 5 6 (Bx1-320 ∷ []) ∷
   re 0 6 (Bx3-1420 ∷ []) ∷ []) Eq.refl

-- sym-ab @03243240: 18 steps
lem-sym-ab-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym-ab-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-4120 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q107 c4) ∷
   rw 2 (q106 c4) ∷
   re 4 1 (Bx3-40 ∷ []) ∷
   re 7 1 (Bx3-40 ∷ []) ∷
   re 2 6 (Bx4-320 ∷ []) ∷
   re 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q107 c4) ∷
   rw 5 (q106 c4) ∷
   re 7 1 (Bx3-40 ∷ []) ∷
   re 10 1 (Bx3-40 ∷ []) ∷
   re 5 6 (Bx4-320 ∷ []) ∷
   re 0 6 (Bx3-4120 ∷ []) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ134 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ014 ∷ []) (wp1014 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (Sw03 ∷ Toff014 ∷ []) (Toff314 ∷ Sw03 ∷ []) (wp1015 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (wl1210 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (Sw03 ∷ Toff324 ∷ []) (Toff024 ∷ Sw03 ∷ []) (wp1016 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CS01 ∷ Sw03 ∷ []) (Sw03 ∷ CS13 ∷ []) (wl1211 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CS01⁻ ∷ Sw03 ∷ []) (Sw03 ∷ CS13⁻ ∷ []) (wl1212 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (Sw03 ∷ Sw03 ∷ []) [] (wl0928 (lit c4))

-- nat-S @01143043: 31 steps
lem-nat-S-at01143043 : Ws → ⟪ (Sw03 ∷ Sb0-1-42-3 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-nat-S-at01143043 c4 = derive (Sw03 ∷ Sb0-1-42-3 ∷ Sw03 ∷ []) (Sb3-1-42-0 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   rw⁻ 0 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   re 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 5 1 (CZ13 ∷ []) ∷
   re 8 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q110 c4) ∷
   re 4 1 (Bx3-10 ∷ []) ∷
   re 7 1 (Bx3-10 ∷ []) ∷
   re 2 6 (Bx1-320 ∷ []) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   re 6 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   re 8 1 (CZ13 ∷ []) ∷
   re 11 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q110 c4) ∷
   re 7 1 (Bx3-10 ∷ []) ∷
   re 10 1 (Bx3-10 ∷ []) ∷
   re 5 6 (Bx1-320 ∷ []) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 7 (q112 c4) ∷
   rw 8 (q111 c4) ∷
   rw⁻ 9 (q113 c4) ∷
   rw 10 (q114 c4) ∷
   re 0 6 (Bx3-1420 ∷ []) ∷
   re 2 1 (Sb3-1-0-2 ∷ []) ∷
   re 4 1 (Sb⁻3-1-0-2 ∷ []) ∷
   re 0 5 (Sb3-1-42-0 ∷ []) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ134 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ123 ∷ []) (wl1216 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Sw24 ∷ Toff312 ∷ []) (Toff314 ∷ Sw24 ∷ []) (wl1217 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (CCZ123 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ134 ∷ []) (wl1218 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Sw24 ∷ Toff134 ∷ []) (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (Bx3-10 ∷ Sw24 ∷ []) (Sw24 ∷ Bx3-10 ∷ []) (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))
  q120 : Ws → Eqn
  q120 c4 = eqn (Sw24 ∷ Sw24 ∷ []) [] (wl0322 (lit c4))

-- nat-SWbc @033440: 23 steps
lem-nat-SWbc-at033440 : Ws → ⟪ (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-nat-SWbc-at033440 c4 = derive (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (Bx3-1420 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) ∷
   rw⁻ 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   re 3 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   rw⁻ 2 (q117 c4) ∷
   rw 3 (q118 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 5 (q118 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   rw 8 (q116 c4) ∷
   rw⁻ 9 (q115 c4) ∷
   re 11 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   rw⁻ 10 (q117 c4) ∷
   rw 11 (q118 c4) ∷
   rw⁻ 12 (q119 c4) ∷
   rw 13 (q118 c4) ∷
   rw⁻ 14 (q117 c4) ∷
   rw⁻ 15 (q119 c4) ∷
   rw 16 (q120 c4) ∷
   re 2 6 (Bx1-320 ∷ []) ∷
   re 5 6 (Bx1-320 ∷ []) ∷
   re 0 6 (Bx3-1420 ∷ []) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Sw24 ∷ Toff314 ∷ []) (Toff312 ∷ Sw24 ∷ []) (wl1231 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (Sw24 ∷ Toff123 ∷ []) (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4))

-- nat-SWbc @03243240: 23 steps
lem-nat-SWbc-at03243240 : Ws → ⟪ (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-nat-SWbc-at03243240 c4 = derive (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (Bx3-1240 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) ∷
   rw⁻ 0 (q117 c4) ∷
   rw 1 (q121 c4) ∷
   re 3 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   rw⁻ 2 (q115 c4) ∷
   rw 3 (q122 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 5 (q122 c4) ∷
   rw⁻ 6 (q115 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   rw 8 (q121 c4) ∷
   rw⁻ 9 (q117 c4) ∷
   re 11 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   rw⁻ 10 (q115 c4) ∷
   rw 11 (q122 c4) ∷
   rw⁻ 12 (q119 c4) ∷
   rw 13 (q122 c4) ∷
   rw⁻ 14 (q115 c4) ∷
   rw⁻ 15 (q119 c4) ∷
   rw 16 (q120 c4) ∷
   re 2 6 (Bx1-340 ∷ []) ∷
   re 5 6 (Bx1-340 ∷ []) ∷
   re 0 6 (Bx3-1240 ∷ []) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = eqn (CCZ034 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ023 ∷ []) (wp0177 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (Sw24 ∷ Toff302 ∷ []) (Toff304 ∷ Sw24 ∷ []) (wp0178 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ023 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ034 ∷ []) (wp0175 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (Sw24 ∷ Toff034 ∷ []) (Toff023 ∷ Sw24 ∷ []) (wp0176 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (Bx3-01 ∷ Sw24 ∷ []) (Sw24 ∷ Bx3-01 ∷ []) (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))

-- nat-SWbc @03103441: 23 steps
lem-nat-SWbc-at03103441 : Ws → ⟪ (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-nat-SWbc-at03103441 c4 = derive (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (Bx3-0421 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) ∷
   rw⁻ 0 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   re 3 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   rw⁻ 2 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw 5 (q126 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw⁻ 7 (q127 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 9 (q123 c4) ∷
   re 11 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   rw⁻ 10 (q125 c4) ∷
   rw 11 (q126 c4) ∷
   rw⁻ 12 (q127 c4) ∷
   rw 13 (q126 c4) ∷
   rw⁻ 14 (q125 c4) ∷
   rw⁻ 15 (q127 c4) ∷
   rw 16 (q120 c4) ∷
   re 2 6 (Bx0-321 ∷ []) ∷
   re 5 6 (Bx0-321 ∷ []) ∷
   re 0 6 (Bx3-0421 ∷ []) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (Sw24 ∷ Toff304 ∷ []) (Toff302 ∷ Sw24 ∷ []) (wp0274 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (Sw24 ∷ Toff023 ∷ []) (Toff034 ∷ Sw24 ∷ []) (wp0273 c4)

-- nat-SWbc @0310243241: 23 steps
lem-nat-SWbc-at0310243241 : Ws → ⟪ (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-nat-SWbc-at0310243241 c4 = derive (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (Bx3-0241 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) ∷
   rw⁻ 0 (q125 c4) ∷
   rw 1 (q128 c4) ∷
   re 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   rw⁻ 2 (q123 c4) ∷
   rw 3 (q129 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw 5 (q129 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw⁻ 7 (q127 c4) ∷
   rw 8 (q128 c4) ∷
   rw⁻ 9 (q125 c4) ∷
   re 11 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   rw⁻ 10 (q123 c4) ∷
   rw 11 (q129 c4) ∷
   rw⁻ 12 (q127 c4) ∷
   rw 13 (q129 c4) ∷
   rw⁻ 14 (q123 c4) ∷
   rw⁻ 15 (q127 c4) ∷
   rw 16 (q120 c4) ∷
   re 2 6 (Bx0-341 ∷ []) ∷
   re 5 6 (Bx0-341 ∷ []) ∷
   re 0 6 (Bx3-0241 ∷ []) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ234 ∷ CS03 ∷ []) (CS03 ∷ CCZ234 ∷ []) (wp0294 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ234 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ234 ∷ []) (wl0432 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (CCZ234 ∷ CS13 ∷ []) (CS13 ∷ CCZ234 ∷ []) (wl0433 (lit c4))

-- cQ @0310213442: 7 steps
lem-cQ-at0310213442 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at0310213442 c4 = derive (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  (rw 0 (q130 c4) ∷
   rw⁻ 4 (q131 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 2 (q133 c4) ∷
   rw 1 (q132 c4) ∷
   rw⁻ 0 (q134 c4) ∷
   rw⁻ 1 (q130 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (CCZ134 ∷ []) (wl1303 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ134 ∷ []) (wp0262 c4)

-- sym-ab @03122031: 18 steps
lem-sym-ab-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym-ab-at03122031 c4 = derive (Bx3-2014 ∷ []) (Bx3-0214 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) ∷
   re 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q135 c4) ∷
   rw⁻ 2 (q136 c4) ∷
   re 4 1 (Bx3-04 ∷ []) ∷
   re 7 1 (Bx3-04 ∷ []) ∷
   re 2 6 (Bx0-314 ∷ []) ∷
   re 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q135 c4) ∷
   rw⁻ 5 (q136 c4) ∷
   re 7 1 (Bx3-04 ∷ []) ∷
   re 10 1 (Bx3-04 ∷ []) ∷
   re 5 6 (Bx0-314 ∷ []) ∷
   re 0 6 (Bx3-0214 ∷ []) ∷ []) Eq.refl

-- sym-ab @0312243041: 18 steps
lem-sym-ab-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym-ab-at0312243041 c4 = derive (Bx3-2401 ∷ []) (Bx3-4201 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 2 (q88 c4) ∷
   re 4 1 (Bx3-41 ∷ []) ∷
   re 7 1 (Bx3-41 ∷ []) ∷
   re 2 6 (Bx4-301 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q89 c4) ∷
   rw 5 (q88 c4) ∷
   re 7 1 (Bx3-41 ∷ []) ∷
   re 10 1 (Bx3-41 ∷ []) ∷
   re 5 6 (Bx4-301 ∷ []) ∷
   re 0 6 (Bx3-4201 ∷ []) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0330 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ012 ∷ CX43 ∷ []) (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀))
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ012 ∷ []) (wl0331 (lit c4))

-- cQ @0214233041: 7 steps
lem-cQ-at0214233041 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0214233041 c4 = derive (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  (rw 0 (q137 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 3 (q138 c4) ∷
   rw⁻ 2 (q139 c4) ∷
   rw⁻ 1 (q138 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw⁻ 1 (q137 c4) ∷ []) Eq.refl

-- sym-ab @0214233041: 18 steps
lem-sym-ab-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-sym-ab-at0214233041 c4 = derive (Bx2-4301 ∷ []) (Bx2-3401 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   re 4 1 (Bx2-31 ∷ []) ∷
   re 7 1 (Bx2-31 ∷ []) ∷
   re 2 6 (Bx3-201 ∷ []) ∷
   re 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   re 7 1 (Bx2-31 ∷ []) ∷
   re 10 1 (Bx2-31 ∷ []) ∷
   re 5 6 (Bx3-201 ∷ []) ∷
   re 0 6 (Bx2-3401 ∷ []) ∷ []) Eq.refl

-- sym-ab @03143041: 18 steps
lem-sym-ab-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym-ab-at03143041 c4 = derive (Bx3-4201 ∷ []) (Bx3-2401 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   re 4 1 (Bx3-21 ∷ []) ∷
   re 7 1 (Bx3-21 ∷ []) ∷
   re 2 6 (Bx2-301 ∷ []) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q88 c4) ∷
   rw 5 (q89 c4) ∷
   re 7 1 (Bx3-21 ∷ []) ∷
   re 10 1 (Bx3-21 ∷ []) ∷
   re 5 6 (Bx2-301 ∷ []) ∷
   re 0 6 (Bx3-2401 ∷ []) ∷ []) Eq.refl

-- sym-ab @0213243041: 18 steps
lem-sym-ab-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-sym-ab-at0213243041 c4 = derive (Bx2-3401 ∷ []) (Bx2-4301 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 2 (q5 c4) ∷
   re 4 1 (Bx2-41 ∷ []) ∷
   re 7 1 (Bx2-41 ∷ []) ∷
   re 2 6 (Bx4-201 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 5 (q5 c4) ∷
   re 7 1 (Bx2-41 ∷ []) ∷
   re 10 1 (Bx2-41 ∷ []) ∷
   re 5 6 (Bx4-201 ∷ []) ∷
   re 0 6 (Bx2-4301 ∷ []) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (CCZ123 ∷ []) (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (CCZ123 ∷ []) (wl1155 (lit c4))

-- sym-ab @02142041: 18 steps
lem-sym-ab-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym-ab-at02142041 c4 = derive (Bx2-4031 ∷ []) (Bx2-0431 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q140 c4) ∷
   rw⁻ 2 (q141 c4) ∷
   re 4 1 (Bx2-01 ∷ []) ∷
   re 7 1 (Bx2-01 ∷ []) ∷
   re 2 6 (Bx0-231 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 5 (q141 c4) ∷
   re 7 1 (Bx2-01 ∷ []) ∷
   re 10 1 (Bx2-01 ∷ []) ∷
   re 5 6 (Bx0-231 ∷ []) ∷
   re 0 6 (Bx2-0431 ∷ []) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0030 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4))
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0135 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (Sw01 ∷ Bx2-34 ∷ []) (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))
  q147 : Ws → Eqn
  q147 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0018 (lit c4))

-- nat-SWbc @02132130: 23 steps
lem-nat-SWbc-at02132130 : Ws → ⟪ (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-nat-SWbc-at02132130 c4 = derive (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (Bx2-3014 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) ∷
   rw⁻ 0 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   re 3 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   rw⁻ 2 (q144 c4) ∷
   rw 3 (q145 c4) ∷
   rw 4 (q146 c4) ∷
   rw 5 (q145 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw 7 (q146 c4) ∷
   rw 8 (q143 c4) ∷
   rw⁻ 9 (q142 c4) ∷
   re 11 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   rw⁻ 10 (q144 c4) ∷
   rw 11 (q145 c4) ∷
   rw 12 (q146 c4) ∷
   rw 13 (q145 c4) ∷
   rw⁻ 14 (q144 c4) ∷
   rw 15 (q146 c4) ∷
   rw 16 (q147 c4) ∷
   re 2 6 (Bx3-214 ∷ []) ∷
   re 5 6 (Bx3-214 ∷ []) ∷
   re 0 6 (Bx2-3014 ∷ []) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = eqn (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4))

-- nat-SWbc @02132031: 23 steps
lem-nat-SWbc-at02132031 : Ws → ⟪ (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-nat-SWbc-at02132031 c4 = derive (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (Bx2-3104 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) ∷
   rw⁻ 0 (q144 c4) ∷
   rw 1 (q148 c4) ∷
   re 3 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   rw⁻ 2 (q142 c4) ∷
   rw 3 (q149 c4) ∷
   rw 4 (q146 c4) ∷
   rw 5 (q149 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw 7 (q146 c4) ∷
   rw 8 (q148 c4) ∷
   rw⁻ 9 (q144 c4) ∷
   re 11 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   rw⁻ 10 (q142 c4) ∷
   rw 11 (q149 c4) ∷
   rw 12 (q146 c4) ∷
   rw 13 (q149 c4) ∷
   rw⁻ 14 (q142 c4) ∷
   rw 15 (q146 c4) ∷
   rw 16 (q147 c4) ∷
   re 2 6 (Bx3-204 ∷ []) ∷
   re 5 6 (Bx3-204 ∷ []) ∷
   re 0 6 (Bx2-3104 ∷ []) ∷ []) Eq.refl

-- sym-ab @02102441: 18 steps
lem-sym-ab-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym-ab-at02102441 c4 = derive (Bx2-0431 ∷ []) (Bx2-4031 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q141 c4) ∷
   rw 2 (q140 c4) ∷
   re 4 1 (Bx2-41 ∷ []) ∷
   re 7 1 (Bx2-41 ∷ []) ∷
   re 2 6 (Bx4-231 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q141 c4) ∷
   rw 5 (q140 c4) ∷
   re 7 1 (Bx2-41 ∷ []) ∷
   re 10 1 (Bx2-41 ∷ []) ∷
   re 5 6 (Bx4-231 ∷ []) ∷
   re 0 6 (Bx2-4031 ∷ []) ∷ []) Eq.refl

-- cQ @0213243041: 7 steps
lem-cQ-at0213243041 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0213243041 c4 = derive (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  (rw 0 (q12 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q12 c4) ∷ []) Eq.refl

-- sym-ab @0314203241: 18 steps
lem-sym-ab-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym-ab-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-0421 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q140 c4) ∷
   rw⁻ 2 (q141 c4) ∷
   re 4 1 (Bx3-01 ∷ []) ∷
   re 7 1 (Bx3-01 ∷ []) ∷
   re 2 6 (Bx0-321 ∷ []) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q140 c4) ∷
   rw⁻ 5 (q141 c4) ∷
   re 7 1 (Bx3-01 ∷ []) ∷
   re 10 1 (Bx3-01 ∷ []) ∷
   re 5 6 (Bx0-321 ∷ []) ∷
   re 0 6 (Bx3-0421 ∷ []) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (Sw01 ∷ Bx3-24 ∷ []) (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat-SWbc @03122130: 23 steps
lem-nat-SWbc-at03122130 : Ws → ⟪ (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-nat-SWbc-at03122130 c4 = derive (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (Bx3-2014 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) ∷
   rw⁻ 0 (q142 c4) ∷
   rw 1 (q149 c4) ∷
   re 3 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   rw⁻ 2 (q144 c4) ∷
   rw 3 (q148 c4) ∷
   rw 4 (q150 c4) ∷
   rw 5 (q148 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw 7 (q150 c4) ∷
   rw 8 (q149 c4) ∷
   rw⁻ 9 (q142 c4) ∷
   re 11 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   rw⁻ 10 (q144 c4) ∷
   rw 11 (q148 c4) ∷
   rw 12 (q150 c4) ∷
   rw 13 (q148 c4) ∷
   rw⁻ 14 (q144 c4) ∷
   rw 15 (q150 c4) ∷
   rw 16 (q147 c4) ∷
   re 2 6 (Bx2-314 ∷ []) ∷
   re 5 6 (Bx2-314 ∷ []) ∷
   re 0 6 (Bx3-2014 ∷ []) ∷ []) Eq.refl

-- nat-SWbc @03122031: 23 steps
lem-nat-SWbc-at03122031 : Ws → ⟪ (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-nat-SWbc-at03122031 c4 = derive (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (Bx3-2104 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) ∷
   rw⁻ 0 (q144 c4) ∷
   rw 1 (q145 c4) ∷
   re 3 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   rw⁻ 2 (q142 c4) ∷
   rw 3 (q143 c4) ∷
   rw 4 (q150 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw 7 (q150 c4) ∷
   rw 8 (q145 c4) ∷
   rw⁻ 9 (q144 c4) ∷
   re 11 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   rw⁻ 10 (q142 c4) ∷
   rw 11 (q143 c4) ∷
   rw 12 (q150 c4) ∷
   rw 13 (q143 c4) ∷
   rw⁻ 14 (q142 c4) ∷
   rw 15 (q150 c4) ∷
   rw 16 (q147 c4) ∷
   re 2 6 (Bx2-304 ∷ []) ∷
   re 5 6 (Bx2-304 ∷ []) ∷
   re 0 6 (Bx3-2104 ∷ []) ∷ []) Eq.refl

-- sym-ab @0310243241: 18 steps
lem-sym-ab-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym-ab-at0310243241 c4 = derive (Bx3-0421 ∷ []) (Bx3-4021 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q141 c4) ∷
   rw 2 (q140 c4) ∷
   re 4 1 (Bx3-41 ∷ []) ∷
   re 7 1 (Bx3-41 ∷ []) ∷
   re 2 6 (Bx4-321 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q141 c4) ∷
   rw 5 (q140 c4) ∷
   re 7 1 (Bx3-41 ∷ []) ∷
   re 10 1 (Bx3-41 ∷ []) ∷
   re 5 6 (Bx4-321 ∷ []) ∷
   re 0 6 (Bx3-4021 ∷ []) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) (wp0008 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) (wp0111 c4)

-- sym-ab @0330: 18 steps
lem-sym-ab-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-sym-ab-at0330 c4 = derive (Bx3-1204 ∷ []) (Bx3-2104 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q151 c4) ∷
   rw⁻ 2 (q152 c4) ∷
   re 4 1 (Bx3-24 ∷ []) ∷
   re 7 1 (Bx3-24 ∷ []) ∷
   re 2 6 (Bx2-304 ∷ []) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q151 c4) ∷
   rw⁻ 5 (q152 c4) ∷
   re 7 1 (Bx3-24 ∷ []) ∷
   re 10 1 (Bx3-24 ∷ []) ∷
   re 5 6 (Bx2-304 ∷ []) ∷
   re 0 6 (Bx3-2104 ∷ []) ∷ []) Eq.refl

-- sym-ab @022330: 18 steps
lem-sym-ab-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym-ab-at022330 c4 = derive (Bx2-1304 ∷ []) (Bx2-3104 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw 2 (q28 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   re 4 1 (Bx2-34 ∷ []) ∷
   re 7 1 (Bx2-34 ∷ []) ∷
   re 2 6 (Bx3-204 ∷ []) ∷
   re 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw 5 (q28 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   re 7 1 (Bx2-34 ∷ []) ∷
   re 10 1 (Bx2-34 ∷ []) ∷
   re 5 6 (Bx3-204 ∷ []) ∷
   re 0 6 (Bx2-3104 ∷ []) ∷ []) Eq.refl

-- sym-ab @03122130: 18 steps
lem-sym-ab-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym-ab-at03122130 c4 = derive (Bx3-2104 ∷ []) (Bx3-1204 ∷ [])
  (re 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) ∷
   re 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw 2 (q152 c4) ∷
   rw⁻ 2 (q151 c4) ∷
   re 4 1 (Bx3-14 ∷ []) ∷
   re 7 1 (Bx3-14 ∷ []) ∷
   re 2 6 (Bx1-304 ∷ []) ∷
   re 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw 5 (q152 c4) ∷
   rw⁻ 5 (q151 c4) ∷
   re 7 1 (Bx3-14 ∷ []) ∷
   re 10 1 (Bx3-14 ∷ []) ∷
   re 5 6 (Bx1-304 ∷ []) ∷
   re 0 6 (Bx3-1204 ∷ []) ∷ []) Eq.refl
