{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E15 where

open import Data.Product.Base using (_,_ )
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.MissingK.Model
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E10 using (e174 ; matrix174 ; w174)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E14 using (e233 ; e236 ; matrix233 ; matrix236 ; w233 ; w236)

w240 : Word Gen
w240 = w233 • w174
matrix240 : Mat 3
matrix240 = mat ((((((0 , 0) , (0 , 0)) , ((16 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((16 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step240 : mulM matrix233 matrix174 ≡ matrix240
step240 = Eq.refl
e240 : readM w240 ≡ matrix240
e240 = Eq.trans (readM-• w233 w174) (Eq.trans (Eq.cong₂ mulM {x = readM w233} {y = matrix233} {u = readM w174} {v = matrix174} e233 e174) step240)

w241 : Word Gen
w241 = w236 • w240
matrix241 : Mat 3
matrix241 = mat ((((((4 , 13) , (13 , 4)) , ((12 , 13) , (13 , 13))) , (((13 , 5) , (4 , 13)) , ((4 , 4) , (4 , 4)))) , ((((13 , 4) , (5 , 13)) , ((4 , 4) , (4 , 4))) , (((4 , 13) , (13 , 5)) , ((13 , 13) , (13 , 13))))) , (((((12 , 4) , (4 , 13)) , ((4 , 4) , (4 , 4))) , (((13 , 4) , (4 , 13)) , ((4 , 5) , (4 , 4)))) , ((((13 , 4) , (4 , 13)) , ((4 , 4) , (5 , 4))) , (((13 , 4) , (4 , 13)) , ((4 , 4) , (4 , 5))))))
step241 : mulM matrix236 matrix240 ≡ matrix241
step241 = Eq.refl
e241 : readM w241 ≡ matrix241
e241 = Eq.trans (readM-• w236 w240) (Eq.trans (Eq.cong₂ mulM {x = readM w236} {y = matrix236} {u = readM w240} {v = matrix240} e236 e240) step241)

