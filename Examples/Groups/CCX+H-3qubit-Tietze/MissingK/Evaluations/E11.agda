{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E11 where

open import Data.Product.Base using (_,_ )
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.MissingK.Model
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E00 using (e5 ; e6 ; matrix5 ; matrix6 ; w5 ; w6)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E03 using (e56 ; matrix56 ; w56)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E07 using (e125 ; matrix125 ; w125)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E08 using (e130 ; e132 ; e137 ; e140 ; matrix130 ; matrix132 ; matrix137 ; matrix140 ; w130 ; w132 ; w137 ; w140)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E10 using (e175 ; matrix175 ; w175)

w176 : Word Gen
w176 = w6 • w175
matrix176 : Mat 3
matrix176 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((9 , 9) , (9 , 9))) , (((0 , 0) , (0 , 0)) , ((9 , 8) , (9 , 8)))) , ((((0 , 0) , (0 , 0)) , ((9 , 9) , (8 , 8))) , (((0 , 0) , (0 , 0)) , ((9 , 8) , (8 , 9))))))
step176 : mulM matrix6 matrix175 ≡ matrix176
step176 = Eq.refl
e176 : readM w176 ≡ matrix176
e176 = Eq.trans (readM-• w6 w175) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w175} {v = matrix175} e6 e175) step176)

w177 : Word Gen
w177 = w132 • w176
matrix177 : Mat 3
matrix177 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((9 , 9) , (9 , 9))) , (((0 , 0) , (0 , 0)) , ((9 , 8) , (9 , 8)))) , ((((0 , 0) , (0 , 0)) , ((9 , 9) , (8 , 8))) , (((0 , 0) , (0 , 0)) , ((9 , 8) , (8 , 9))))))
step177 : mulM matrix132 matrix176 ≡ matrix177
step177 = Eq.refl
e177 : readM w177 ≡ matrix177
e177 = Eq.trans (readM-• w132 w176) (Eq.trans (Eq.cong₂ mulM {x = readM w132} {y = matrix132} {u = readM w176} {v = matrix176} e132 e176) step177)

w178 : Word Gen
w178 = w176 • w132
matrix178 : Mat 3
matrix178 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((9 , 9) , (9 , 9))) , (((0 , 0) , (0 , 0)) , ((9 , 8) , (9 , 8)))) , ((((0 , 0) , (0 , 0)) , ((9 , 9) , (8 , 8))) , (((0 , 0) , (0 , 0)) , ((9 , 8) , (8 , 9))))))
step178 : mulM matrix176 matrix132 ≡ matrix178
step178 = Eq.refl
e178 : readM w178 ≡ matrix178
e178 = Eq.trans (readM-• w176 w132) (Eq.trans (Eq.cong₂ mulM {x = readM w176} {y = matrix176} {u = readM w132} {v = matrix132} e176 e132) step178)

w179 : Word Gen
w179 = w56 • w125
matrix179 : Mat 3
matrix179 = mat ((((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1)))) , ((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))) , (((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))))))
step179 : mulM matrix56 matrix125 ≡ matrix179
step179 = Eq.refl
e179 : readM w179 ≡ matrix179
e179 = Eq.trans (readM-• w56 w125) (Eq.trans (Eq.cong₂ mulM {x = readM w56} {y = matrix56} {u = readM w125} {v = matrix125} e56 e125) step179)

w180 : Word Gen
w180 = w5 • w179
matrix180 : Mat 3
matrix180 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step180 : mulM matrix5 matrix179 ≡ matrix180
step180 = Eq.refl
e180 : readM w180 ≡ matrix180
e180 = Eq.trans (readM-• w5 w179) (Eq.trans (Eq.cong₂ mulM {x = readM w5} {y = matrix5} {u = readM w179} {v = matrix179} e5 e179) step180)

w181 : Word Gen
w181 = w6 • w180
matrix181 : Mat 3
matrix181 = mat ((((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step181 : mulM matrix6 matrix180 ≡ matrix181
step181 = Eq.refl
e181 : readM w181 ≡ matrix181
e181 = Eq.trans (readM-• w6 w180) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w180} {v = matrix180} e6 e180) step181)

w182 : Word Gen
w182 = w181 • w132
matrix182 : Mat 3
matrix182 = mat ((((((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step182 : mulM matrix181 matrix132 ≡ matrix182
step182 = Eq.refl
e182 : readM w182 ≡ matrix182
e182 = Eq.trans (readM-• w181 w132) (Eq.trans (Eq.cong₂ mulM {x = readM w181} {y = matrix181} {u = readM w132} {v = matrix132} e181 e132) step182)

w183 : Word Gen
w183 = w140 • w137
matrix183 : Mat 3
matrix183 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step183 : mulM matrix140 matrix137 ≡ matrix183
step183 = Eq.refl
e183 : readM w183 ≡ matrix183
e183 = Eq.trans (readM-• w140 w137) (Eq.trans (Eq.cong₂ mulM {x = readM w140} {y = matrix140} {u = readM w137} {v = matrix137} e140 e137) step183)

w184 : Word Gen
w184 = w137 • w183
matrix184 : Mat 3
matrix184 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step184 : mulM matrix137 matrix183 ≡ matrix184
step184 = Eq.refl
e184 : readM w184 ≡ matrix184
e184 = Eq.trans (readM-• w137 w183) (Eq.trans (Eq.cong₂ mulM {x = readM w137} {y = matrix137} {u = readM w183} {v = matrix183} e137 e183) step184)

w185 : Word Gen
w185 = w130 • w181
matrix185 : Mat 3
matrix185 = mat ((((((0 , 16) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step185 : mulM matrix130 matrix181 ≡ matrix185
step185 = Eq.refl
e185 : readM w185 ≡ matrix185
e185 = Eq.trans (readM-• w130 w181) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w181} {v = matrix181} e130 e181) step185)

w186 : Word Gen
w186 = w181 • w185
matrix186 : Mat 3
matrix186 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 16) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step186 : mulM matrix181 matrix185 ≡ matrix186
step186 = Eq.refl
e186 : readM w186 ≡ matrix186
e186 = Eq.trans (readM-• w181 w185) (Eq.trans (Eq.cong₂ mulM {x = readM w181} {y = matrix181} {u = readM w185} {v = matrix185} e181 e185) step186)

w187 : Word Gen
w187 = w137 • w140
matrix187 : Mat 3
matrix187 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step187 : mulM matrix137 matrix140 ≡ matrix187
step187 = Eq.refl
e187 : readM w187 ≡ matrix187
e187 = Eq.trans (readM-• w137 w140) (Eq.trans (Eq.cong₂ mulM {x = readM w137} {y = matrix137} {u = readM w140} {v = matrix140} e137 e140) step187)

w188 : Word Gen
w188 = w181 • w187
matrix188 : Mat 3
matrix188 = mat ((((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step188 : mulM matrix181 matrix187 ≡ matrix188
step188 = Eq.refl
e188 : readM w188 ≡ matrix188
e188 = Eq.trans (readM-• w181 w187) (Eq.trans (Eq.cong₂ mulM {x = readM w181} {y = matrix181} {u = readM w187} {v = matrix187} e181 e187) step188)

w189 : Word Gen
w189 = w130 • w188
matrix189 : Mat 3
matrix189 = mat ((((((0 , 0) , (0 , 16)) , ((0 , 0) , (0 , 0))) , (((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step189 : mulM matrix130 matrix188 ≡ matrix189
step189 = Eq.refl
e189 : readM w189 ≡ matrix189
e189 = Eq.trans (readM-• w130 w188) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w188} {v = matrix188} e130 e188) step189)

w190 : Word Gen
w190 = w181 • w189
matrix190 : Mat 3
matrix190 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 16)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step190 : mulM matrix181 matrix189 ≡ matrix190
step190 = Eq.refl
e190 : readM w190 ≡ matrix190
e190 = Eq.trans (readM-• w181 w189) (Eq.trans (Eq.cong₂ mulM {x = readM w181} {y = matrix181} {u = readM w189} {v = matrix189} e181 e189) step190)

w191 : Word Gen
w191 = w137 • w190
matrix191 : Mat 3
matrix191 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 16)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step191 : mulM matrix137 matrix190 ≡ matrix191
step191 = Eq.refl
e191 : readM w191 ≡ matrix191
e191 = Eq.trans (readM-• w137 w190) (Eq.trans (Eq.cong₂ mulM {x = readM w137} {y = matrix137} {u = readM w190} {v = matrix190} e137 e190) step191)

