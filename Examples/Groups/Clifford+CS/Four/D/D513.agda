{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD513 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D513 (W : Ws) (Sᴰ : SD513) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ123-CCZ023 : St 8
  lem-comm-CCZ123-CCZ023 = pickᴰ 0 Sᴰ
  lem-pass-S0-vs-CS03 : St 62
  lem-pass-S0-vs-CS03 = pickᴰ 1 Sᴰ
  lem-pass-CS13-vs-S0 : St 63
  lem-pass-CS13-vs-S0 = pickᴰ 2 Sᴰ
  lem-pass-CSd13-vs-S0 : St 64
  lem-pass-CSd13-vs-S0 = pickᴰ 3 Sᴰ
  lem-pass-CS12-vs-CSd03 : St 34
  lem-pass-CS12-vs-CSd03 = pickᴰ 4 Sᴰ
  lem-pass-CSd12-vs-CSd03 : St 56
  lem-pass-CSd12-vs-CSd03 = pickᴰ 5 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS02 : St 65
  lem-pass-X3-CSd30-X3-vs-CS02 = pickᴰ 6 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CSd02 : St 66
  lem-pass-X3-CSd30-X3-vs-CSd02 = pickᴰ 7 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF013 : St 67
  lem-pass-X3-CSd30-X3-vs-TOFF013 = pickᴰ 8 Sᴰ
  lem-comm-CCZ012-CCZ123 : St 68
  lem-comm-CCZ012-CCZ123 = pickᴰ 9 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS13 : St 69
  lem-pass-X2-CK20-X2-vs-CS13 = pickᴰ 10 Sᴰ
  lem-pass-X2-CK20-X2-vs-CSd13 : St 70
  lem-pass-X2-CK20-X2-vs-CSd13 = pickᴰ 11 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF102 : St 71
  lem-pass-X2-CK20-X2-vs-TOFF102 = pickᴰ 12 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS13 : St 72
  lem-pass-X2-CKd20-X2-vs-CS13 = pickᴰ 13 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CSd13 : St 73
  lem-pass-X2-CKd20-X2-vs-CSd13 = pickᴰ 14 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF102 : St 74
  lem-pass-X2-CKd20-X2-vs-TOFF102 = pickᴰ 15 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03 : St 75
  lem-pass-X2-CS20-X2-vs-CS03 = pickᴰ 16 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS13 : St 76
  lem-pass-X2-CS20-X2-vs-CS13 = pickᴰ 17 Sᴰ
  lem-pass-X2-CS20-X2-vs-CSd03 : St 77
  lem-pass-X2-CS20-X2-vs-CSd03 = pickᴰ 18 Sᴰ
  lem-pass-X2-CS20-X2-vs-CSd13 : St 78
  lem-pass-X2-CS20-X2-vs-CSd13 = pickᴰ 19 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF012 : St 79
  lem-pass-X2-CS20-X2-vs-TOFF012 = pickᴰ 20 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF102 : St 80
  lem-pass-X2-CS20-X2-vs-TOFF102 = pickᴰ 21 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS13 : St 81
  lem-pass-X2-CSd20-X2-vs-CS13 = pickᴰ 22 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CSd13 : St 82
  lem-pass-X2-CSd20-X2-vs-CSd13 = pickᴰ 23 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF102 : St 83
  lem-pass-X2-CSd20-X2-vs-TOFF102 = pickᴰ 24 Sᴰ
  lem-comm-CCZ023-CS01 : St 84
  lem-comm-CCZ023-CS01 = pickᴰ 25 Sᴰ
  lem-comm-CCZ023-CSd13 : St 85
  lem-comm-CCZ023-CSd13 = pickᴰ 26 Sᴰ
  lem-pass-S0-vs-CS01 : St 86
  lem-pass-S0-vs-CS01 = pickᴰ 27 Sᴰ
  lem-pass-S0-vs-CSd01 : St 87
  lem-pass-S0-vs-CSd01 = pickᴰ 28 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 88
  lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 29 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS02 : St 89
  lem-pass-X3-CS31-X3-vs-CS02 = pickᴰ 30 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS12 : St 90
  lem-pass-X3-CS31-X3-vs-CS12 = pickᴰ 31 Sᴰ
  lem-pass-X3-CS31-X3-vs-CSd12 : St 91
  lem-pass-X3-CS31-X3-vs-CSd12 = pickᴰ 32 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF103 : St 92
  lem-pass-X3-CS31-X3-vs-TOFF103 = pickᴰ 33 Sᴰ
  lem-pass-S0-vs-CS12 : St 93
  lem-pass-S0-vs-CS12 = pickᴰ 34 Sᴰ
  lem-pass-S0-vs-CSd12 : St 94
  lem-pass-S0-vs-CSd12 = pickᴰ 35 Sᴰ
  lem-pass-X1-CS10-X1-vs-TOFF012 : St 95
  lem-pass-X1-CS10-X1-vs-TOFF012 = pickᴰ 36 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS03 : St 96
  lem-pass-X2-CK21-X2-vs-CS03 = pickᴰ 37 Sᴰ
  lem-pass-X2-CK21-X2-vs-CSd03 : St 97
  lem-pass-X2-CK21-X2-vs-CSd03 = pickᴰ 38 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF012 : St 98
  lem-pass-X2-CK21-X2-vs-TOFF012 = pickᴰ 39 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS03 : St 99
  lem-pass-X2-CKd21-X2-vs-CS03 = pickᴰ 40 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CSd03 : St 100
  lem-pass-X2-CKd21-X2-vs-CSd03 = pickᴰ 41 Sᴰ
  lem-pass-X2-CKd21-X2-vs-TOFF012 : St 101
  lem-pass-X2-CKd21-X2-vs-TOFF012 = pickᴰ 42 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS03 : St 102
  lem-pass-X2-CS21-X2-vs-CS03 = pickᴰ 43 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS13 : St 103
  lem-pass-X2-CS21-X2-vs-CS13 = pickᴰ 44 Sᴰ
  lem-pass-X2-CS21-X2-vs-CSd03 : St 104
  lem-pass-X2-CS21-X2-vs-CSd03 = pickᴰ 45 Sᴰ
  lem-pass-X2-CS21-X2-vs-CSd13 : St 105
  lem-pass-X2-CS21-X2-vs-CSd13 = pickᴰ 46 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF012 : St 106
  lem-pass-X2-CS21-X2-vs-TOFF012 = pickᴰ 47 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102 : St 107
  lem-pass-X2-CS21-X2-vs-TOFF102 = pickᴰ 48 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03 : St 108
  lem-pass-X2-CSd20-X2-vs-CS03 = pickᴰ 49 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CSd03 : St 109
  lem-pass-X2-CSd20-X2-vs-CSd03 = pickᴰ 50 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF012 : St 110
  lem-pass-X2-CSd20-X2-vs-TOFF012 = pickᴰ 51 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS03 : St 111
  lem-pass-X2-CSd21-X2-vs-CS03 = pickᴰ 52 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CSd03 : St 112
  lem-pass-X2-CSd21-X2-vs-CSd03 = pickᴰ 53 Sᴰ
  lem-pass-X2-CSd21-X2-vs-TOFF012 : St 113
  lem-pass-X2-CSd21-X2-vs-TOFF012 = pickᴰ 54 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS02 : St 114
  lem-pass-X3-CK31-X3-vs-CS02 = pickᴰ 55 Sᴰ
  lem-pass-X3-CK31-X3-vs-CSd02 : St 115
  lem-pass-X3-CK31-X3-vs-CSd02 = pickᴰ 56 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF013 : St 116
  lem-pass-X3-CK31-X3-vs-TOFF013 = pickᴰ 57 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS02 : St 117
  lem-pass-X3-CKd31-X3-vs-CS02 = pickᴰ 58 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CSd02 : St 118
  lem-pass-X3-CKd31-X3-vs-CSd02 = pickᴰ 59 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF013 : St 119
  lem-pass-X3-CKd31-X3-vs-TOFF013 = pickᴰ 60 Sᴰ
  lem-pass-X3-CS31-X3-vs-CSd02 : St 120
  lem-pass-X3-CS31-X3-vs-CSd02 = pickᴰ 61 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF013 : St 121
  lem-pass-X3-CS31-X3-vs-TOFF013 = pickᴰ 62 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS02 : St 122
  lem-pass-X3-CSd31-X3-vs-CS02 = pickᴰ 63 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CSd02 : St 123
  lem-pass-X3-CSd31-X3-vs-CSd02 = pickᴰ 64 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF013 : St 124
  lem-pass-X3-CSd31-X3-vs-TOFF013 = pickᴰ 65 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03 : St 125
  lem-pass-X1-CS10-X1-vs-CS03 = pickᴰ 66 Sᴰ
  lem-pass-X1-CS10-X1-vs-CSd03 : St 126
  lem-pass-X1-CS10-X1-vs-CSd03 = pickᴰ 67 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS13 : St 127
  lem-pass-X2-CSd21-X2-vs-CS13 = pickᴰ 68 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CSd13 : St 128
  lem-pass-X2-CSd21-X2-vs-CSd13 = pickᴰ 69 Sᴰ
  lem-pass-X2-CSd21-X2-vs-TOFF102 : St 129
  lem-pass-X2-CSd21-X2-vs-TOFF102 = pickᴰ 70 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS12 : St 130
  lem-pass-X3-CSd31-X3-vs-CS12 = pickᴰ 71 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CSd12 : St 131
  lem-pass-X3-CSd31-X3-vs-CSd12 = pickᴰ 72 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF103 : St 132
  lem-pass-X3-CSd31-X3-vs-TOFF103 = pickᴰ 73 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS12 : St 133
  lem-pass-X3-CS32-X3-vs-CS12 = pickᴰ 74 Sᴰ
  lem-pass-X3-CS32-X3-vs-CSd12 : St 134
  lem-pass-X3-CS32-X3-vs-CSd12 = pickᴰ 75 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF203 : St 135
  lem-pass-X3-CS32-X3-vs-TOFF203 = pickᴰ 76 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 136
  lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 77 Sᴰ
  lem-comm-CCZ012-CS23 : St 137
  lem-comm-CCZ012-CS23 = pickᴰ 78 Sᴰ
  lem-comm-CCZ013-CS23 : St 138
  lem-comm-CCZ013-CS23 = pickᴰ 79 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS01 : St 139
  lem-pass-X3-CKd32-X3-vs-CS01 = pickᴰ 80 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CSd01 : St 140
  lem-pass-X3-CKd32-X3-vs-CSd01 = pickᴰ 81 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF023 : St 141
  lem-pass-X3-CKd32-X3-vs-TOFF023 = pickᴰ 82 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS01 : St 142
  lem-pass-X3-CS32-X3-vs-CS01 = pickᴰ 83 Sᴰ
  lem-pass-X3-CS32-X3-vs-CSd01 : St 143
  lem-pass-X3-CS32-X3-vs-CSd01 = pickᴰ 84 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF023 : St 144
  lem-pass-X3-CS32-X3-vs-TOFF023 = pickᴰ 85 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS01 : St 145
  lem-pass-X3-CSd32-X3-vs-CS01 = pickᴰ 86 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS12 : St 146
  lem-pass-X3-CSd32-X3-vs-CS12 = pickᴰ 87 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CSd01 : St 147
  lem-pass-X3-CSd32-X3-vs-CSd01 = pickᴰ 88 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CSd12 : St 148
  lem-pass-X3-CSd32-X3-vs-CSd12 = pickᴰ 89 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF023 : St 149
  lem-pass-X3-CSd32-X3-vs-TOFF023 = pickᴰ 90 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF203 : St 150
  lem-pass-X3-CSd32-X3-vs-TOFF203 = pickᴰ 91 Sᴰ

private
  q1 : Eqn
  q1 = sE 67 lem-pass-X3-CSd30-X3-vs-TOFF013
  q2 : Eqn
  q2 = sE 65 lem-pass-X3-CSd30-X3-vs-CS02
  q3 : Eqn
  q3 = sE 66 lem-pass-X3-CSd30-X3-vs-CSd02

-- pass [X3 CSd30 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丞丮丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丞丮丞乞丧乞丨") (ℓ "乞丧乞丨丞丮丞")
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q1 ∷
   rw 3 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 68 lem-comm-CCZ012-CCZ123

-- pass [CCZ012] [CCZ123]: 1 steps
lem-pass-CCZ012-vs-CCZ123 : ⟪ (ℓ "乙乜") ⟫ʷ ≈ ⟪ (ℓ "乜乙") ⟫ʷ
lem-pass-CCZ012-vs-CCZ123 = derive (ℓ "乙乜") (ℓ "乜乙")
  (rw 0 q4 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = sE 79 lem-pass-X2-CS20-X2-vs-TOFF012
  q6 : Eqn
  q6 = sE 75 lem-pass-X2-CS20-X2-vs-CS03
  q7 : Eqn
  q7 = sE 77 lem-pass-X2-CS20-X2-vs-CSd03

-- pass [X2 CS20 X2] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丘丧丘九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丘丧丘九中九丮") (ℓ "九中九丮丘丧丘")
  (rw 0 q5 ∷
   rw 1 q6 ∷
   rw 2 q5 ∷
   rw 3 q7 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = sE 80 lem-pass-X2-CS20-X2-vs-TOFF102
  q9 : Eqn
  q9 = sE 76 lem-pass-X2-CS20-X2-vs-CS13
  q10 : Eqn
  q10 = sE 78 lem-pass-X2-CS20-X2-vs-CSd13

-- pass [X2 CS20 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘丧丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘丧丘习丽习举") (ℓ "习丽习举丘丧丘")
  (rw 0 q8 ∷
   rw 1 q9 ∷
   rw 2 q8 ∷
   rw 3 q10 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = sE 71 lem-pass-X2-CK20-X2-vs-TOFF102
  q12 : Eqn
  q12 = sE 69 lem-pass-X2-CK20-X2-vs-CS13
  q13 : Eqn
  q13 = sE 70 lem-pass-X2-CK20-X2-vs-CSd13

-- pass [X2 CK20 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘乄丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘乄丘习丽习举") (ℓ "习丽习举丘乄丘")
  (rw 0 q11 ∷
   rw 1 q12 ∷
   rw 2 q11 ∷
   rw 3 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 74 lem-pass-X2-CKd20-X2-vs-TOFF102
  q15 : Eqn
  q15 = sE 72 lem-pass-X2-CKd20-X2-vs-CS13
  q16 : Eqn
  q16 = sE 73 lem-pass-X2-CKd20-X2-vs-CSd13

-- pass [X2 CKd20 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘久丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘久丘习丽习举") (ℓ "习丽习举丘久丘")
  (rw 0 q14 ∷
   rw 1 q15 ∷
   rw 2 q14 ∷
   rw 3 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = sE 83 lem-pass-X2-CSd20-X2-vs-TOFF102
  q18 : Eqn
  q18 = sE 81 lem-pass-X2-CSd20-X2-vs-CS13
  q19 : Eqn
  q19 = sE 82 lem-pass-X2-CSd20-X2-vs-CSd13

-- pass [X2 CSd20 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘丨丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘丨丘习丽习举") (ℓ "习丽习举丘丨丘")
  (rw 0 q17 ∷
   rw 1 q18 ∷
   rw 2 q17 ∷
   rw 3 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 8 lem-comm-CCZ123-CCZ023

-- pass [CCZ123] [CCZ023]: 1 steps
lem-pass-CCZ123-vs-CCZ023 : ⟪ (ℓ "乜乛") ⟫ʷ ≈ ⟪ (ℓ "乛乜") ⟫ʷ
lem-pass-CCZ123-vs-CCZ023 = derive (ℓ "乜乛") (ℓ "乛乜")
  (rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = sE 85 lem-comm-CCZ023-CSd13

-- pass [CCZ023] [CSd13]: 1 steps
lem-pass-CCZ023-vs-CSd13 : ⟪ (ℓ "乛举") ⟫ʷ ≈ ⟪ (ℓ "举乛") ⟫ʷ
lem-pass-CCZ023-vs-CSd13 = derive (ℓ "乛举") (ℓ "举乛")
  (rw 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = sE 62 lem-pass-S0-vs-CS03

-- pass [CS03] [S0]: 1 steps
lem-pass-CS03-vs-S0 : ⟪ (ℓ "中丈") ⟫ʷ ≈ ⟪ (ℓ "丈中") ⟫ʷ
lem-pass-CS03-vs-S0 = derive (ℓ "中丈") (ℓ "丈中")
  (rw⁻ 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 84 lem-comm-CCZ023-CS01

-- pass [CCZ023] [CS01]: 1 steps
lem-pass-CCZ023-vs-CS01 : ⟪ (ℓ "乛丠") ⟫ʷ ≈ ⟪ (ℓ "丠乛") ⟫ʷ
lem-pass-CCZ023-vs-CS01 = derive (ℓ "乛丠") (ℓ "丠乛")
  (rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = sE 92 lem-pass-X3-CS31-X3-vs-TOFF103
  q25 : Eqn
  q25 = sE 90 lem-pass-X3-CS31-X3-vs-CS12
  q26 : Eqn
  q26 = sE 91 lem-pass-X3-CS31-X3-vs-CSd12

-- pass [X3 CS31 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (ℓ "丞丽丞乡丶乡丷") ⟫ʷ ≈ ⟪ (ℓ "乡丶乡丷丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (ℓ "丞丽丞乡丶乡丷") (ℓ "乡丶乡丷丞丽丞")
  (rw 0 q24 ∷
   rw 1 q25 ∷
   rw 2 q24 ∷
   rw 3 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = sE 89 lem-pass-X3-CS31-X3-vs-CS02
  q28 : Eqn
  q28 = sE 121 lem-pass-X3-CS31-X3-vs-TOFF013
  q29 : Eqn
  q29 = sE 120 lem-pass-X3-CS31-X3-vs-CSd02

-- pass [X3 CS31 X3] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (ℓ "丞丽丞丧乞丨乞") ⟫ʷ ≈ ⟪ (ℓ "丧乞丨乞丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = derive (ℓ "丞丽丞丧乞丨乞") (ℓ "丧乞丨乞丞丽丞")
  (rw 0 q27 ∷
   rw 1 q28 ∷
   rw 2 q29 ∷
   rw 3 q28 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 114 lem-pass-X3-CK31-X3-vs-CS02
  q31 : Eqn
  q31 = sE 116 lem-pass-X3-CK31-X3-vs-TOFF013
  q32 : Eqn
  q32 = sE 115 lem-pass-X3-CK31-X3-vs-CSd02

-- pass [X3 CK31 X3] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (ℓ "丞乔丞丧乞丨乞") ⟫ʷ ≈ ⟪ (ℓ "丧乞丨乞丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = derive (ℓ "丞乔丞丧乞丨乞") (ℓ "丧乞丨乞丞乔丞")
  (rw 0 q30 ∷
   rw 1 q31 ∷
   rw 2 q32 ∷
   rw 3 q31 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 117 lem-pass-X3-CKd31-X3-vs-CS02
  q34 : Eqn
  q34 = sE 119 lem-pass-X3-CKd31-X3-vs-TOFF013
  q35 : Eqn
  q35 = sE 118 lem-pass-X3-CKd31-X3-vs-CSd02

-- pass [X3 CKd31 X3] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (ℓ "丞乕丞丧乞丨乞") ⟫ʷ ≈ ⟪ (ℓ "丧乞丨乞丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = derive (ℓ "丞乕丞丧乞丨乞") (ℓ "丧乞丨乞丞乕丞")
  (rw 0 q33 ∷
   rw 1 q34 ∷
   rw 2 q35 ∷
   rw 3 q34 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 122 lem-pass-X3-CSd31-X3-vs-CS02
  q37 : Eqn
  q37 = sE 124 lem-pass-X3-CSd31-X3-vs-TOFF013
  q38 : Eqn
  q38 = sE 123 lem-pass-X3-CSd31-X3-vs-CSd02

-- pass [X3 CSd31 X3] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (ℓ "丞举丞丧乞丨乞") ⟫ʷ ≈ ⟪ (ℓ "丧乞丨乞丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = derive (ℓ "丞举丞丧乞丨乞") (ℓ "丧乞丨乞丞举丞")
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 2 q38 ∷
   rw 3 q37 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 110 lem-pass-X2-CSd20-X2-vs-TOFF012
  q40 : Eqn
  q40 = sE 108 lem-pass-X2-CSd20-X2-vs-CS03
  q41 : Eqn
  q41 = sE 109 lem-pass-X2-CSd20-X2-vs-CSd03

-- pass [X2 CSd20 X2] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丘丨丘九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丘丨丘九中九丮") (ℓ "九中九丮丘丨丘")
  (rw 0 q39 ∷
   rw 1 q40 ∷
   rw 2 q39 ∷
   rw 3 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = sE 107 lem-pass-X2-CS21-X2-vs-TOFF102
  q43 : Eqn
  q43 = sE 103 lem-pass-X2-CS21-X2-vs-CS13
  q44 : Eqn
  q44 = sE 105 lem-pass-X2-CS21-X2-vs-CSd13

-- pass [X2 CS21 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘丶丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘丶丘习丽习举") (ℓ "习丽习举丘丶丘")
  (rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q42 ∷
   rw 3 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = sE 102 lem-pass-X2-CS21-X2-vs-CS03
  q46 : Eqn
  q46 = sE 106 lem-pass-X2-CS21-X2-vs-TOFF012
  q47 : Eqn
  q47 = sE 104 lem-pass-X2-CS21-X2-vs-CSd03

-- pass [X2 CS21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘丶丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘丶丘中九丮九") (ℓ "中九丮九丘丶丘")
  (rw 0 q45 ∷
   rw 1 q46 ∷
   rw 2 q47 ∷
   rw 3 q46 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = sE 96 lem-pass-X2-CK21-X2-vs-CS03
  q49 : Eqn
  q49 = sE 98 lem-pass-X2-CK21-X2-vs-TOFF012
  q50 : Eqn
  q50 = sE 97 lem-pass-X2-CK21-X2-vs-CSd03

-- pass [X2 CK21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘乇丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘乇丘中九丮九") (ℓ "中九丮九丘乇丘")
  (rw 0 q48 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   rw 3 q49 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = sE 99 lem-pass-X2-CKd21-X2-vs-CS03
  q52 : Eqn
  q52 = sE 101 lem-pass-X2-CKd21-X2-vs-TOFF012
  q53 : Eqn
  q53 = sE 100 lem-pass-X2-CKd21-X2-vs-CSd03

-- pass [X2 CKd21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘么丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘么丘中九丮九") (ℓ "中九丮九丘么丘")
  (rw 0 q51 ∷
   rw 1 q52 ∷
   rw 2 q53 ∷
   rw 3 q52 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 111 lem-pass-X2-CSd21-X2-vs-CS03
  q55 : Eqn
  q55 = sE 113 lem-pass-X2-CSd21-X2-vs-TOFF012
  q56 : Eqn
  q56 = sE 112 lem-pass-X2-CSd21-X2-vs-CSd03

-- pass [X2 CSd21 X2] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘丷丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘丷丘中九丮九") (ℓ "中九丮九丘丷丘")
  (rw 0 q54 ∷
   rw 1 q55 ∷
   rw 2 q56 ∷
   rw 3 q55 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 1366 W
  q58 : Eqn
  q58 = sE 88 lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q59 : Eqn
  q59 = wE 1367 W

-- pass [CK31] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 3 steps
lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (ℓ "乔丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞乔") ⟫ʷ
lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (ℓ "乔丞习丽习举丞") (ℓ "丞习丽习举丞乔")
  (rw 0 q57 ∷
   rw 1 q58 ∷
   rw 5 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 1368 W
  q61 : Eqn
  q61 = sE 63 lem-pass-CS13-vs-S0
  q62 : Eqn
  q62 = sE 64 lem-pass-CSd13-vs-S0

-- pass [S0] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丈习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丈") ⟫ʷ
lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丈习丽习举") (ℓ "习丽习举丈")
  (rw 0 q60 ∷
   rw⁻ 1 q61 ∷
   rw 2 q60 ∷
   rw⁻ 3 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 1 W
  q64 : Eqn
  q64 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q65 : Eqn
  q65 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q66 : Eqn
  q66 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q67 : Eqn
  q67 = wE 3 W
  q68 : Eqn
  q68 = wE 196 W
  q69 : Eqn
  q69 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q70 : Eqn
  q70 = sE 93 lem-pass-S0-vs-CS12
  q71 : Eqn
  q71 = sE 94 lem-pass-S0-vs-CSd12

-- pass [S0] [TOFF103 CS12 TOFF103 CSd12]: 120 steps
lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (ℓ "丈乡丶乡丷") ⟫ʷ ≈ ⟪ (ℓ "乡丶乡丷丈") ⟫ʷ
lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12 = derive (ℓ "丈乡丶乡丷") (ℓ "乡丶乡丷丈")
  (rw 2 q63 ∷
   re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q64 ∷
   rw 4 q63 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q65 ∷
   rw 6 q63 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q65 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q64 ∷
   rw⁻ 8 q66 ∷
   rw 9 q67 ∷
   rw 8 q66 ∷
   rw 7 q64 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q67 ∷
   rw 5 q65 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q67 ∷
   rw 3 q65 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q67 ∷
   rw 1 q64 ∷
   rw 2 q68 ∷
   re 2 8 (ℓ "习") ∷
   rw 0 q69 ∷
   rw 1 q60 ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q64 ∷
   rw 3 q63 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q65 ∷
   rw 5 q63 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q65 ∷
   rw 7 q63 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q64 ∷
   rw⁻ 7 q66 ∷
   rw 0 q63 ∷
   rw⁻ 1 q64 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q67 ∷
   rw⁻ 3 q65 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q67 ∷
   rw⁻ 5 q65 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q67 ∷
   rw⁻ 7 q64 ∷
   rw⁻ 8 q66 ∷
   rw 1 q68 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw⁻ 1 q69 ∷
   rw 2 q67 ∷
   rw 1 q70 ∷
   rw 4 q63 ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q64 ∷
   rw 6 q63 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q65 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q65 ∷
   rw 10 q63 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q64 ∷
   rw⁻ 10 q66 ∷
   rw 11 q67 ∷
   rw 10 q66 ∷
   rw 9 q64 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q67 ∷
   rw 7 q65 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q67 ∷
   rw 5 q65 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q67 ∷
   rw 3 q64 ∷
   rw 4 q68 ∷
   re 4 8 (ℓ "习") ∷
   rw 2 q69 ∷
   rw 3 q60 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q64 ∷
   rw 5 q63 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q65 ∷
   rw 7 q63 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q65 ∷
   rw 9 q63 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q64 ∷
   rw⁻ 9 q66 ∷
   rw 2 q63 ∷
   rw⁻ 3 q64 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q67 ∷
   rw⁻ 5 q65 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q67 ∷
   rw⁻ 7 q65 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q67 ∷
   rw⁻ 9 q64 ∷
   rw⁻ 10 q66 ∷
   rw 3 q68 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw⁻ 3 q69 ∷
   rw 4 q67 ∷
   rw 3 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 1352 W
  q73 : Eqn
  q73 = sE 34 lem-pass-CS12-vs-CSd03
  q74 : Eqn
  q74 = sE 56 lem-pass-CSd12-vs-CSd03

-- pass [CSd03] [TOFF103 CS12 TOFF103 CSd12]: 124 steps
lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (ℓ "丮乡丶乡丷") ⟫ʷ ≈ ⟪ (ℓ "乡丶乡丷丮") ⟫ʷ
lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12 = derive (ℓ "丮乡丶乡丷") (ℓ "乡丶乡丷丮")
  (rw 2 q63 ∷
   re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q64 ∷
   rw 4 q63 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q65 ∷
   rw 6 q63 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q65 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q64 ∷
   rw⁻ 8 q66 ∷
   rw 9 q67 ∷
   rw 8 q66 ∷
   rw 7 q64 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q67 ∷
   rw 5 q65 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q67 ∷
   rw 3 q65 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q67 ∷
   rw 1 q64 ∷
   rw 2 q68 ∷
   re 2 8 (ℓ "习") ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q67 ∷
   rw 1 q72 ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q64 ∷
   rw 3 q63 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q65 ∷
   rw 5 q63 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q65 ∷
   rw 7 q63 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q64 ∷
   rw⁻ 7 q66 ∷
   rw 0 q63 ∷
   rw⁻ 1 q64 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q67 ∷
   rw⁻ 3 q65 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q67 ∷
   rw⁻ 5 q65 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q67 ∷
   rw⁻ 7 q64 ∷
   rw⁻ 8 q66 ∷
   rw 1 q68 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 3 q63 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q67 ∷
   rw⁻ 1 q73 ∷
   rw 4 q63 ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q64 ∷
   rw 6 q63 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q65 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q65 ∷
   rw 10 q63 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q64 ∷
   rw⁻ 10 q66 ∷
   rw 11 q67 ∷
   rw 10 q66 ∷
   rw 9 q64 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q67 ∷
   rw 7 q65 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q67 ∷
   rw 5 q65 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q67 ∷
   rw 3 q64 ∷
   rw 4 q68 ∷
   re 4 8 (ℓ "习") ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q67 ∷
   rw 3 q72 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q64 ∷
   rw 5 q63 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q65 ∷
   rw 7 q63 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q65 ∷
   rw 9 q63 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q64 ∷
   rw⁻ 9 q66 ∷
   rw 2 q63 ∷
   rw⁻ 3 q64 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q67 ∷
   rw⁻ 5 q65 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q67 ∷
   rw⁻ 7 q65 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q67 ∷
   rw⁻ 9 q64 ∷
   rw⁻ 10 q66 ∷
   rw 3 q68 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw 5 q63 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q67 ∷
   rw⁻ 3 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = eqn (ℓ "丈乢") (ℓ "乢丈") (low₁-comm (S) (Toff))
  q76 : Eqn
  q76 = sE 86 lem-pass-S0-vs-CS01
  q77 : Eqn
  q77 = sE 87 lem-pass-S0-vs-CSd01

-- pass [S0] [TOFF123 CS01 TOFF123 CSd01]: 4 steps
lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01 : ⟪ (ℓ "丈乢丠乢両") ⟫ʷ ≈ ⟪ (ℓ "乢丠乢両丈") ⟫ʷ
lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01 = derive (ℓ "丈乢丠乢両") (ℓ "乢丠乢両丈")
  (rw 0 q75 ∷
   rw 1 q76 ∷
   rw 2 q75 ∷
   rw 3 q77 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = sE 95 lem-pass-X1-CS10-X1-vs-TOFF012
  q79 : Eqn
  q79 = sE 125 lem-pass-X1-CS10-X1-vs-CS03
  q80 : Eqn
  q80 = sE 126 lem-pass-X1-CS10-X1-vs-CSd03

-- pass [X1 CS10 X1] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丒丠丒九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丒丠丒九中九丮") (ℓ "九中九丮丒丠丒")
  (rw 0 q78 ∷
   rw 1 q79 ∷
   rw 2 q78 ∷
   rw 3 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 225 W
  q82 : Eqn
  q82 = wE 1369 W
  q83 : Eqn
  q83 = sE 88 lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q84 : Eqn
  q84 = wE 390 W
  q85 : Eqn
  q85 = wE 1370 W

-- pass [X3 CKd31 X3] [TOFF102 CS13 TOFF102 CSd13]: 7 steps
lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞乕丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞乕丞习丽习举") (ℓ "习丽习举丞乕丞")
  (rw 7 q81 ∷
   rw 8 q82 ∷
   rw 9 q81 ∷
   rw⁻ 3 q83 ∷
   rw 2 q84 ∷
   rw 1 q85 ∷
   rw 0 q84 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = sE 132 lem-pass-X3-CSd31-X3-vs-TOFF103
  q87 : Eqn
  q87 = sE 130 lem-pass-X3-CSd31-X3-vs-CS12
  q88 : Eqn
  q88 = sE 131 lem-pass-X3-CSd31-X3-vs-CSd12

-- pass [X3 CSd31 X3] [TOFF103 CS12 TOFF103 CSd12]: 4 steps
lem-pass-X3-CSd31-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (ℓ "丞举丞乡丶乡丷") ⟫ʷ ≈ ⟪ (ℓ "乡丶乡丷丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (ℓ "丞举丞乡丶乡丷") (ℓ "乡丶乡丷丞举丞")
  (rw 0 q86 ∷
   rw 1 q87 ∷
   rw 2 q86 ∷
   rw 3 q88 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = sE 129 lem-pass-X2-CSd21-X2-vs-TOFF102
  q90 : Eqn
  q90 = sE 127 lem-pass-X2-CSd21-X2-vs-CS13
  q91 : Eqn
  q91 = sE 128 lem-pass-X2-CSd21-X2-vs-CSd13

-- pass [X2 CSd21 X2] [TOFF102 CS13 TOFF102 CSd13]: 4 steps
lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丘丷丘习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丘丷丘习丽习举") (ℓ "习丽习举丘丷丘")
  (rw 0 q89 ∷
   rw 1 q90 ∷
   rw 2 q89 ∷
   rw 3 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = sE 135 lem-pass-X3-CS32-X3-vs-TOFF203
  q93 : Eqn
  q93 = sE 133 lem-pass-X3-CS32-X3-vs-CS12
  q94 : Eqn
  q94 = sE 134 lem-pass-X3-CS32-X3-vs-CSd12

-- pass [X3 CS32 X3] [TOFF203 CS12 TOFF203 CSd12]: 4 steps
lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12 : ⟪ (ℓ "丞义丞乤丶乤丷") ⟫ʷ ≈ ⟪ (ℓ "乤丶乤丷丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12 = derive (ℓ "丞义丞乤丶乤丷") (ℓ "乤丶乤丷丞义丞")
  (rw 0 q92 ∷
   rw 1 q93 ∷
   rw 2 q92 ∷
   rw 3 q94 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = wE 1371 W
  q96 : Eqn
  q96 = sE 136 lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q97 : Eqn
  q97 = wE 1372 W

-- pass [X3 CKd32 X3] [TOFF201 CS23 TOFF201 CSd23]: 7 steps
lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "丞乘丞乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "丞乘丞乣义乣乊") (ℓ "乣义乣乊丞乘丞")
  (rw 7 q81 ∷
   rw 8 q95 ∷
   rw 9 q81 ∷
   rw⁻ 3 q96 ∷
   rw 2 q84 ∷
   rw 1 q97 ∷
   rw 0 q84 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = sE 150 lem-pass-X3-CSd32-X3-vs-TOFF203
  q99 : Eqn
  q99 = sE 146 lem-pass-X3-CSd32-X3-vs-CS12
  q100 : Eqn
  q100 = sE 148 lem-pass-X3-CSd32-X3-vs-CSd12

-- pass [X3 CSd32 X3] [TOFF203 CS12 TOFF203 CSd12]: 4 steps
lem-pass-X3-CSd32-X3-vs-TOFF203-CS12-TOFF203-CSd12 : ⟪ (ℓ "丞乊丞乤丶乤丷") ⟫ʷ ≈ ⟪ (ℓ "乤丶乤丷丞乊丞") ⟫ʷ
lem-pass-X3-CSd32-X3-vs-TOFF203-CS12-TOFF203-CSd12 = derive (ℓ "丞乊丞乤丶乤丷") (ℓ "乤丶乤丷丞乊丞")
  (rw 0 q98 ∷
   rw 1 q99 ∷
   rw 2 q98 ∷
   rw 3 q100 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = sE 149 lem-pass-X3-CSd32-X3-vs-TOFF023
  q102 : Eqn
  q102 = sE 145 lem-pass-X3-CSd32-X3-vs-CS01
  q103 : Eqn
  q103 = sE 147 lem-pass-X3-CSd32-X3-vs-CSd01

-- pass [X3 CSd32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CSd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (ℓ "丞乊丞也丠也両") ⟫ʷ ≈ ⟪ (ℓ "也丠也両丞乊丞") ⟫ʷ
lem-pass-X3-CSd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = derive (ℓ "丞乊丞也丠也両") (ℓ "也丠也両丞乊丞")
  (rw 0 q101 ∷
   rw 1 q102 ∷
   rw 2 q101 ∷
   rw 3 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = sE 141 lem-pass-X3-CKd32-X3-vs-TOFF023
  q105 : Eqn
  q105 = sE 139 lem-pass-X3-CKd32-X3-vs-CS01
  q106 : Eqn
  q106 = sE 140 lem-pass-X3-CKd32-X3-vs-CSd01

-- pass [X3 CKd32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CKd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (ℓ "丞乘丞也丠也両") ⟫ʷ ≈ ⟪ (ℓ "也丠也両丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = derive (ℓ "丞乘丞也丠也両") (ℓ "也丠也両丞乘丞")
  (rw 0 q104 ∷
   rw 1 q105 ∷
   rw 2 q104 ∷
   rw 3 q106 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = sE 144 lem-pass-X3-CS32-X3-vs-TOFF023
  q108 : Eqn
  q108 = sE 142 lem-pass-X3-CS32-X3-vs-CS01
  q109 : Eqn
  q109 = sE 143 lem-pass-X3-CS32-X3-vs-CSd01

-- pass [X3 CS32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CS32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (ℓ "丞义丞也丠也両") ⟫ʷ ≈ ⟪ (ℓ "也丠也両丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = derive (ℓ "丞义丞也丠也両") (ℓ "也丠也両丞义丞")
  (rw 0 q107 ∷
   rw 1 q108 ∷
   rw 2 q107 ∷
   rw 3 q109 ∷ []) Eq.refl

private
  q110 : Eqn
  q110 = sE 137 lem-comm-CCZ012-CS23

-- pass [CCZ012] [CS23]: 1 steps
lem-pass-CCZ012-vs-CS23 : ⟪ (ℓ "乙义") ⟫ʷ ≈ ⟪ (ℓ "义乙") ⟫ʷ
lem-pass-CCZ012-vs-CS23 = derive (ℓ "乙义") (ℓ "义乙")
  (rw 0 q110 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = sE 138 lem-comm-CCZ013-CS23

-- pass [CCZ013] [CS23]: 1 steps
lem-pass-CCZ013-vs-CS23 : ⟪ (ℓ "乚义") ⟫ʷ ≈ ⟪ (ℓ "义乚") ⟫ʷ
lem-pass-CCZ013-vs-CS23 = derive (ℓ "乚义") (ℓ "义乚")
  (rw 0 q111 ∷ []) Eq.refl
