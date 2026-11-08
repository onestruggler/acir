{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E08 where

open import Data.Product.Base using (_,_ )
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.MissingK.Model
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E00 using (e5 ; e6 ; matrix5 ; matrix6 ; w5 ; w6)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E02 using (e47 ; matrix47 ; w47)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E03 using (e50 ; e56 ; matrix50 ; matrix56 ; w50 ; w56)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E07 using (e127 ; matrix127 ; w127)

w128 : Word Gen
w128 = w50 • w127
matrix128 : Mat 3
matrix128 = mat ((((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1)))) , ((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))) , (((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))))
step128 : mulM matrix50 matrix127 ≡ matrix128
step128 = Eq.refl
e128 : readM w128 ≡ matrix128
e128 = Eq.trans (readM-• w50 w127) (Eq.trans (Eq.cong₂ mulM {x = readM w50} {y = matrix50} {u = readM w127} {v = matrix127} e50 e127) step128)

w129 : Word Gen
w129 = w5 • w128
matrix129 : Mat 3
matrix129 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step129 : mulM matrix5 matrix128 ≡ matrix129
step129 = Eq.refl
e129 : readM w129 ≡ matrix129
e129 = Eq.trans (readM-• w5 w128) (Eq.trans (Eq.cong₂ mulM {x = readM w5} {y = matrix5} {u = readM w128} {v = matrix128} e5 e128) step129)

w130 : Word Gen
w130 = w6 • w129
matrix130 : Mat 3
matrix130 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step130 : mulM matrix6 matrix129 ≡ matrix130
step130 = Eq.refl
e130 : readM w130 ≡ matrix130
e130 = Eq.trans (readM-• w6 w129) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w129} {v = matrix129} e6 e129) step130)

w131 : Word Gen
w131 = w130 • w130
matrix131 : Mat 3
matrix131 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step131 : mulM matrix130 matrix130 ≡ matrix131
step131 = Eq.refl
e131 : readM w131 ≡ matrix131
e131 = Eq.trans (readM-• w130 w130) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w130} {v = matrix130} e130 e130) step131)

w132 : Word Gen
w132 = NK
matrix132 : Mat 3
matrix132 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
e132 : readM w132 ≡ matrix132
e132 = Eq.trans (readM-gen NK-gen) Eq.refl

w133 : Word Gen
w133 = w132 • w132
matrix133 : Mat 3
matrix133 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step133 : mulM matrix132 matrix132 ≡ matrix133
step133 = Eq.refl
e133 : readM w133 ≡ matrix133
e133 = Eq.trans (readM-• w132 w132) (Eq.trans (Eq.cong₂ mulM {x = readM w132} {y = matrix132} {u = readM w132} {v = matrix132} e132 e132) step133)

w134 : Word Gen
w134 = w56 • w6
matrix134 : Mat 3
matrix134 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))))
step134 : mulM matrix56 matrix6 ≡ matrix134
step134 = Eq.refl
e134 : readM w134 ≡ matrix134
e134 = Eq.trans (readM-• w56 w6) (Eq.trans (Eq.cong₂ mulM {x = readM w56} {y = matrix56} {u = readM w6} {v = matrix6} e56 e6) step134)

w135 : Word Gen
w135 = w47 • w134
matrix135 : Mat 3
matrix135 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))))
step135 : mulM matrix47 matrix134 ≡ matrix135
step135 = Eq.refl
e135 : readM w135 ≡ matrix135
e135 = Eq.trans (readM-• w47 w134) (Eq.trans (Eq.cong₂ mulM {x = readM w47} {y = matrix47} {u = readM w134} {v = matrix134} e47 e134) step135)

w136 : Word Gen
w136 = w56 • w135
matrix136 : Mat 3
matrix136 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step136 : mulM matrix56 matrix135 ≡ matrix136
step136 = Eq.refl
e136 : readM w136 ≡ matrix136
e136 = Eq.trans (readM-• w56 w135) (Eq.trans (Eq.cong₂ mulM {x = readM w56} {y = matrix56} {u = readM w135} {v = matrix135} e56 e135) step136)

w137 : Word Gen
w137 = w6 • w136
matrix137 : Mat 3
matrix137 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step137 : mulM matrix6 matrix136 ≡ matrix137
step137 = Eq.refl
e137 : readM w137 ≡ matrix137
e137 = Eq.trans (readM-• w6 w136) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w136} {v = matrix136} e6 e136) step137)

w138 : Word Gen
w138 = w137 • w130
matrix138 : Mat 3
matrix138 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step138 : mulM matrix137 matrix130 ≡ matrix138
step138 = Eq.refl
e138 : readM w138 ≡ matrix138
e138 = Eq.trans (readM-• w137 w130) (Eq.trans (Eq.cong₂ mulM {x = readM w137} {y = matrix137} {u = readM w130} {v = matrix130} e137 e130) step138)

w139 : Word Gen
w139 = w130 • w137
matrix139 : Mat 3
matrix139 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step139 : mulM matrix130 matrix137 ≡ matrix139
step139 = Eq.refl
e139 : readM w139 ≡ matrix139
e139 = Eq.trans (readM-• w130 w137) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w137} {v = matrix137} e130 e137) step139)

w140 : Word Gen
w140 = w6 • w134
matrix140 : Mat 3
matrix140 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step140 : mulM matrix6 matrix134 ≡ matrix140
step140 = Eq.refl
e140 : readM w140 ≡ matrix140
e140 = Eq.trans (readM-• w6 w134) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w134} {v = matrix134} e6 e134) step140)

w141 : Word Gen
w141 = w140 • w130
matrix141 : Mat 3
matrix141 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step141 : mulM matrix140 matrix130 ≡ matrix141
step141 = Eq.refl
e141 : readM w141 ≡ matrix141
e141 = Eq.trans (readM-• w140 w130) (Eq.trans (Eq.cong₂ mulM {x = readM w140} {y = matrix140} {u = readM w130} {v = matrix130} e140 e130) step141)

w142 : Word Gen
w142 = w130 • w140
matrix142 : Mat 3
matrix142 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step142 : mulM matrix130 matrix140 ≡ matrix142
step142 = Eq.refl
e142 : readM w142 ≡ matrix142
e142 = Eq.trans (readM-• w130 w140) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w140} {v = matrix140} e130 e140) step142)

w143 : Word Gen
w143 = w50 • w6
matrix143 : Mat 3
matrix143 = mat ((((((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))) , (((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))))
step143 : mulM matrix50 matrix6 ≡ matrix143
step143 = Eq.refl
e143 : readM w143 ≡ matrix143
e143 = Eq.trans (readM-• w50 w6) (Eq.trans (Eq.cong₂ mulM {x = readM w50} {y = matrix50} {u = readM w6} {v = matrix6} e50 e6) step143)

