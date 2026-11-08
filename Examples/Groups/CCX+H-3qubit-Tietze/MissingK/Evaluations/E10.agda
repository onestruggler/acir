{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E10 where

open import Data.Product.Base using (_,_ )
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.MissingK.Model
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E00 using (e6 ; matrix6 ; w6)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E03 using (e56 ; matrix56 ; w56)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E07 using (e122 ; matrix122 ; w122)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E08 using (e130 ; e132 ; matrix130 ; matrix132 ; w130 ; w132)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E09 using (e156 ; matrix156 ; w156)

w160 : Word Gen
w160 = w130 • w122
matrix160 : Mat 3
matrix160 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step160 : mulM matrix130 matrix122 ≡ matrix160
step160 = Eq.refl
e160 : readM w160 ≡ matrix160
e160 = Eq.trans (readM-• w130 w122) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w122} {v = matrix122} e130 e122) step160)

w161 : Word Gen
w161 = w56 • w130
matrix161 : Mat 3
matrix161 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))))
step161 : mulM matrix56 matrix130 ≡ matrix161
step161 = Eq.refl
e161 : readM w161 ≡ matrix161
e161 = Eq.trans (readM-• w56 w130) (Eq.trans (Eq.cong₂ mulM {x = readM w56} {y = matrix56} {u = readM w130} {v = matrix130} e56 e130) step161)

w162 : Word Gen
w162 = w130 • w56
matrix162 : Mat 3
matrix162 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))))
step162 : mulM matrix130 matrix56 ≡ matrix162
step162 = Eq.refl
e162 : readM w162 ≡ matrix162
e162 = Eq.trans (readM-• w130 w56) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w56} {v = matrix56} e130 e56) step162)

w163 : Word Gen
w163 = w156 • w132
matrix163 : Mat 3
matrix163 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step163 : mulM matrix156 matrix132 ≡ matrix163
step163 = Eq.refl
e163 : readM w163 ≡ matrix163
e163 = Eq.trans (readM-• w156 w132) (Eq.trans (Eq.cong₂ mulM {x = readM w156} {y = matrix156} {u = readM w132} {v = matrix132} e156 e132) step163)

w164 : Word Gen
w164 = w132 • w156
matrix164 : Mat 3
matrix164 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step164 : mulM matrix132 matrix156 ≡ matrix164
step164 = Eq.refl
e164 : readM w164 ≡ matrix164
e164 = Eq.trans (readM-• w132 w156) (Eq.trans (Eq.cong₂ mulM {x = readM w132} {y = matrix132} {u = readM w156} {v = matrix156} e132 e156) step164)

w165 : Word Gen
w165 = w122 • w132
matrix165 : Mat 3
matrix165 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step165 : mulM matrix122 matrix132 ≡ matrix165
step165 = Eq.refl
e165 : readM w165 ≡ matrix165
e165 = Eq.trans (readM-• w122 w132) (Eq.trans (Eq.cong₂ mulM {x = readM w122} {y = matrix122} {u = readM w132} {v = matrix132} e122 e132) step165)

w166 : Word Gen
w166 = w132 • w122
matrix166 : Mat 3
matrix166 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step166 : mulM matrix132 matrix122 ≡ matrix166
step166 = Eq.refl
e166 : readM w166 ≡ matrix166
e166 = Eq.trans (readM-• w132 w122) (Eq.trans (Eq.cong₂ mulM {x = readM w132} {y = matrix132} {u = readM w122} {v = matrix122} e132 e122) step166)

w167 : Word Gen
w167 = w56 • w132
matrix167 : Mat 3
matrix167 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))))
step167 : mulM matrix56 matrix132 ≡ matrix167
step167 = Eq.refl
e167 : readM w167 ≡ matrix167
e167 = Eq.trans (readM-• w56 w132) (Eq.trans (Eq.cong₂ mulM {x = readM w56} {y = matrix56} {u = readM w132} {v = matrix132} e56 e132) step167)

w168 : Word Gen
w168 = w132 • w56
matrix168 : Mat 3
matrix168 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))))
step168 : mulM matrix132 matrix56 ≡ matrix168
step168 = Eq.refl
e168 : readM w168 ≡ matrix168
e168 = Eq.trans (readM-• w132 w56) (Eq.trans (Eq.cong₂ mulM {x = readM w132} {y = matrix132} {u = readM w56} {v = matrix56} e132 e56) step168)

w169 : Word Gen
w169 = w130 • w6
matrix169 : Mat 3
matrix169 = mat ((((((0 , 0) , (0 , 0)) , ((16 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step169 : mulM matrix130 matrix6 ≡ matrix169
step169 = Eq.refl
e169 : readM w169 ≡ matrix169
e169 = Eq.trans (readM-• w130 w6) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w6} {v = matrix6} e130 e6) step169)

w170 : Word Gen
w170 = w6 • w169
matrix170 : Mat 3
matrix170 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((16 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step170 : mulM matrix6 matrix169 ≡ matrix170
step170 = Eq.refl
e170 : readM w170 ≡ matrix170
e170 = Eq.trans (readM-• w6 w169) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w169} {v = matrix169} e6 e169) step170)

w171 : Word Gen
w171 = w170 • w132
matrix171 : Mat 3
matrix171 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((16 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step171 : mulM matrix170 matrix132 ≡ matrix171
step171 = Eq.refl
e171 : readM w171 ≡ matrix171
e171 = Eq.trans (readM-• w170 w132) (Eq.trans (Eq.cong₂ mulM {x = readM w170} {y = matrix170} {u = readM w132} {v = matrix132} e170 e132) step171)

w172 : Word Gen
w172 = w132 • w170
matrix172 : Mat 3
matrix172 = mat ((((((9 , 9) , (9 , 9)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (9 , 8)) , ((0 , 0) , (0 , 0)))) , ((((9 , 9) , (8 , 8)) , ((0 , 0) , (0 , 0))) , (((9 , 8) , (8 , 9)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((16 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step172 : mulM matrix132 matrix170 ≡ matrix172
step172 = Eq.refl
e172 : readM w172 ≡ matrix172
e172 = Eq.trans (readM-• w132 w170) (Eq.trans (Eq.cong₂ mulM {x = readM w132} {y = matrix132} {u = readM w170} {v = matrix170} e132 e170) step172)

w173 : Word Gen
w173 = w130 • w170
matrix173 : Mat 3
matrix173 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((16 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step173 : mulM matrix130 matrix170 ≡ matrix173
step173 = Eq.refl
e173 : readM w173 ≡ matrix173
e173 = Eq.trans (readM-• w130 w170) (Eq.trans (Eq.cong₂ mulM {x = readM w130} {y = matrix130} {u = readM w170} {v = matrix170} e130 e170) step173)

w174 : Word Gen
w174 = w170 • w130
matrix174 : Mat 3
matrix174 = mat ((((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((16 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step174 : mulM matrix170 matrix130 ≡ matrix174
step174 = Eq.refl
e174 : readM w174 ≡ matrix174
e174 = Eq.trans (readM-• w170 w130) (Eq.trans (Eq.cong₂ mulM {x = readM w170} {y = matrix170} {u = readM w130} {v = matrix130} e170 e130) step174)

w175 : Word Gen
w175 = w132 • w6
matrix175 : Mat 3
matrix175 = mat ((((((0 , 0) , (0 , 0)) , ((9 , 9) , (9 , 9))) , (((0 , 0) , (0 , 0)) , ((9 , 8) , (9 , 8)))) , ((((0 , 0) , (0 , 0)) , ((9 , 9) , (8 , 8))) , (((0 , 0) , (0 , 0)) , ((9 , 8) , (8 , 9))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step175 : mulM matrix132 matrix6 ≡ matrix175
step175 = Eq.refl
e175 : readM w175 ≡ matrix175
e175 = Eq.trans (readM-• w132 w6) (Eq.trans (Eq.cong₂ mulM {x = readM w132} {y = matrix132} {u = readM w6} {v = matrix6} e132 e6) step175)

