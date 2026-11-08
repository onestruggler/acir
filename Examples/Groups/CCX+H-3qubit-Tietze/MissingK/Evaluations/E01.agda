{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E01 where

open import Data.Product.Base using (_,_ )
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.MissingK.Model
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E00 using (e1 ; e2 ; e5 ; e15 ; matrix1 ; matrix2 ; matrix5 ; matrix15 ; w1 ; w2 ; w5 ; w15)

w16 : Word Gen
w16 = w1 • w15
matrix16 : Mat 3
matrix16 = mat ((((((9 , 8) , (0 , 0)) , ((8 , 8) , (0 , 0))) , (((8 , 9) , (0 , 0)) , ((8 , 8) , (0 , 0)))) , ((((0 , 0) , (8 , 9)) , ((0 , 0) , (9 , 9))) , (((0 , 0) , (9 , 8)) , ((0 , 0) , (9 , 9))))) , (((((8 , 8) , (0 , 0)) , ((9 , 8) , (0 , 0))) , (((8 , 8) , (0 , 0)) , ((8 , 9) , (0 , 0)))) , ((((0 , 0) , (9 , 9)) , ((0 , 0) , (8 , 9))) , (((0 , 0) , (9 , 9)) , ((0 , 0) , (9 , 8))))))
step16 : mulM matrix1 matrix15 ≡ matrix16
step16 = Eq.refl
e16 : readM w16 ≡ matrix16
e16 = Eq.trans (readM-• w1 w15) (Eq.trans (Eq.cong₂ mulM {x = readM w1} {y = matrix1} {u = readM w15} {v = matrix15} e1 e15) step16)

w17 : Word Gen
w17 = CX20
matrix17 : Mat 3
matrix17 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
e17 : readM w17 ≡ matrix17
e17 = Eq.trans (readM-gen CX20-gen) Eq.refl

w18 : Word Gen
w18 = CCX12
matrix18 : Mat 3
matrix18 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
e18 : readM w18 ≡ matrix18
e18 = Eq.trans (readM-gen CCX12-gen) Eq.refl

w19 : Word Gen
w19 = w5 • w18
matrix19 : Mat 3
matrix19 = mat ((((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1)))) , ((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))))
step19 : mulM matrix5 matrix18 ≡ matrix19
step19 = Eq.refl
e19 : readM w19 ≡ matrix19
e19 = Eq.trans (readM-• w5 w18) (Eq.trans (Eq.cong₂ mulM {x = readM w5} {y = matrix5} {u = readM w18} {v = matrix18} e5 e18) step19)

w20 : Word Gen
w20 = w18 • w19
matrix20 : Mat 3
matrix20 = mat ((((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1)))) , ((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))))
step20 : mulM matrix18 matrix19 ≡ matrix20
step20 = Eq.refl
e20 : readM w20 ≡ matrix20
e20 = Eq.trans (readM-• w18 w19) (Eq.trans (Eq.cong₂ mulM {x = readM w18} {y = matrix18} {u = readM w19} {v = matrix19} e18 e19) step20)

w21 : Word Gen
w21 = w5 • w20
matrix21 : Mat 3
matrix21 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step21 : mulM matrix5 matrix20 ≡ matrix21
step21 = Eq.refl
e21 : readM w21 ≡ matrix21
e21 = Eq.trans (readM-• w5 w20) (Eq.trans (Eq.cong₂ mulM {x = readM w5} {y = matrix5} {u = readM w20} {v = matrix20} e5 e20) step21)

w22 : Word Gen
w22 = CX21
matrix22 : Mat 3
matrix22 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))))
e22 : readM w22 ≡ matrix22
e22 = Eq.trans (readM-gen CX21-gen) Eq.refl

w23 : Word Gen
w23 = w17 • w2
matrix23 : Mat 3
matrix23 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step23 : mulM matrix17 matrix2 ≡ matrix23
step23 = Eq.refl
e23 : readM w23 ≡ matrix23
e23 = Eq.trans (readM-• w17 w2) (Eq.trans (Eq.cong₂ mulM {x = readM w17} {y = matrix17} {u = readM w2} {v = matrix2} e17 e2) step23)

w24 : Word Gen
w24 = w2 • w23
matrix24 : Mat 3
matrix24 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))))
step24 : mulM matrix2 matrix23 ≡ matrix24
step24 = Eq.refl
e24 : readM w24 ≡ matrix24
e24 = Eq.trans (readM-• w2 w23) (Eq.trans (Eq.cong₂ mulM {x = readM w2} {y = matrix2} {u = readM w23} {v = matrix23} e2 e23) step24)

w25 : Word Gen
w25 = w17 • w24
matrix25 : Mat 3
matrix25 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))))
step25 : mulM matrix17 matrix24 ≡ matrix25
step25 = Eq.refl
e25 : readM w25 ≡ matrix25
e25 = Eq.trans (readM-• w17 w24) (Eq.trans (Eq.cong₂ mulM {x = readM w17} {y = matrix17} {u = readM w24} {v = matrix24} e17 e24) step25)

w26 : Word Gen
w26 = CX12
matrix26 : Mat 3
matrix26 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))))
e26 : readM w26 ≡ matrix26
e26 = Eq.trans (readM-gen CX12-gen) Eq.refl

w27 : Word Gen
w27 = w22 • w1
matrix27 : Mat 3
matrix27 = mat ((((((4 , 13) , (13 , 13)) , ((12 , 4) , (4 , 4))) , (((13 , 4) , (4 , 5)) , ((4 , 13) , (13 , 13)))) , ((((13 , 5) , (4 , 4)) , ((4 , 13) , (13 , 13))) , (((13 , 4) , (5 , 4)) , ((4 , 13) , (13 , 13))))) , (((((12 , 4) , (4 , 4)) , ((4 , 13) , (13 , 13))) , (((4 , 13) , (13 , 13)) , ((13 , 4) , (4 , 5)))) , ((((4 , 13) , (13 , 13)) , ((13 , 5) , (4 , 4))) , (((4 , 13) , (13 , 13)) , ((13 , 4) , (5 , 4))))))
step27 : mulM matrix22 matrix1 ≡ matrix27
step27 = Eq.refl
e27 : readM w27 ≡ matrix27
e27 = Eq.trans (readM-• w22 w1) (Eq.trans (Eq.cong₂ mulM {x = readM w22} {y = matrix22} {u = readM w1} {v = matrix1} e22 e1) step27)

w28 : Word Gen
w28 = w1 • w27
matrix28 : Mat 3
matrix28 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))))
step28 : mulM matrix1 matrix27 ≡ matrix28
step28 = Eq.refl
e28 : readM w28 ≡ matrix28
e28 = Eq.trans (readM-• w1 w27) (Eq.trans (Eq.cong₂ mulM {x = readM w1} {y = matrix1} {u = readM w27} {v = matrix27} e1 e27) step28)

w29 : Word Gen
w29 = SWAP12
matrix29 : Mat 3
matrix29 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
e29 : readM w29 ≡ matrix29
e29 = Eq.trans (readM-gen SWAP12-gen) Eq.refl

w30 : Word Gen
w30 = w22 • w26
matrix30 : Mat 3
matrix30 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))))))
step30 : mulM matrix22 matrix26 ≡ matrix30
step30 = Eq.refl
e30 : readM w30 ≡ matrix30
e30 = Eq.trans (readM-• w22 w26) (Eq.trans (Eq.cong₂ mulM {x = readM w22} {y = matrix22} {u = readM w26} {v = matrix26} e22 e26) step30)

w31 : Word Gen
w31 = w26 • w30
matrix31 : Mat 3
matrix31 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step31 : mulM matrix26 matrix30 ≡ matrix31
step31 = Eq.refl
e31 : readM w31 ≡ matrix31
e31 = Eq.trans (readM-• w26 w30) (Eq.trans (Eq.cong₂ mulM {x = readM w26} {y = matrix26} {u = readM w30} {v = matrix30} e26 e30) step31)

