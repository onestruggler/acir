{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E06 where

open import Data.Product.Base using (_,_ )
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.MissingK.Model
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E00 using (e0 ; e1 ; e2 ; e6 ; e10 ; matrix0 ; matrix1 ; matrix2 ; matrix6 ; matrix10 ; w0 ; w1 ; w2 ; w6 ; w10)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E01 using (e18 ; matrix18 ; w18)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E02 using (e38 ; e41 ; matrix38 ; matrix41 ; w38 ; w41)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E03 using (e56 ; e59 ; e62 ; matrix56 ; matrix59 ; matrix62 ; w56 ; w59 ; w62)
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluations.E04 using (e76 ; matrix76 ; w76)

w96 : Word Gen
w96 = w18 • w41
matrix96 : Mat 3
matrix96 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step96 : mulM matrix18 matrix41 ≡ matrix96
step96 = Eq.refl
e96 : readM w96 ≡ matrix96
e96 = Eq.trans (readM-• w18 w41) (Eq.trans (Eq.cong₂ mulM {x = readM w18} {y = matrix18} {u = readM w41} {v = matrix41} e18 e41) step96)

w97 : Word Gen
w97 = w41 • w18
matrix97 : Mat 3
matrix97 = mat ((((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step97 : mulM matrix41 matrix18 ≡ matrix97
step97 = Eq.refl
e97 : readM w97 ≡ matrix97
e97 = Eq.trans (readM-• w41 w18) (Eq.trans (Eq.cong₂ mulM {x = readM w41} {y = matrix41} {u = readM w18} {v = matrix18} e41 e18) step97)

w98 : Word Gen
w98 = w6 • w18
matrix98 : Mat 3
matrix98 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step98 : mulM matrix6 matrix18 ≡ matrix98
step98 = Eq.refl
e98 : readM w98 ≡ matrix98
e98 = Eq.trans (readM-• w6 w18) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w18} {v = matrix18} e6 e18) step98)

w99 : Word Gen
w99 = w18 • w6
matrix99 : Mat 3
matrix99 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step99 : mulM matrix18 matrix6 ≡ matrix99
step99 = Eq.refl
e99 : readM w99 ≡ matrix99
e99 = Eq.trans (readM-• w18 w6) (Eq.trans (Eq.cong₂ mulM {x = readM w18} {y = matrix18} {u = readM w6} {v = matrix6} e18 e6) step99)

w100 : Word Gen
w100 = w6 • w41
matrix100 : Mat 3
matrix100 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step100 : mulM matrix6 matrix41 ≡ matrix100
step100 = Eq.refl
e100 : readM w100 ≡ matrix100
e100 = Eq.trans (readM-• w6 w41) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w41} {v = matrix41} e6 e41) step100)

w101 : Word Gen
w101 = w41 • w6
matrix101 : Mat 3
matrix101 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))))))
step101 : mulM matrix41 matrix6 ≡ matrix101
step101 = Eq.refl
e101 : readM w101 ≡ matrix101
e101 = Eq.trans (readM-• w41 w6) (Eq.trans (Eq.cong₂ mulM {x = readM w41} {y = matrix41} {u = readM w6} {v = matrix6} e41 e6) step101)

w102 : Word Gen
w102 = w38 • w1
matrix102 : Mat 3
matrix102 = mat ((((((4 , 13) , (12 , 4)) , ((13 , 13) , (4 , 4))) , (((13 , 4) , (4 , 13)) , ((5 , 4) , (13 , 13)))) , ((((12 , 4) , (4 , 13)) , ((4 , 4) , (13 , 13))) , (((4 , 13) , (13 , 4)) , ((13 , 13) , (5 , 4))))) , (((((13 , 5) , (4 , 13)) , ((4 , 4) , (13 , 13))) , (((13 , 4) , (4 , 13)) , ((4 , 5) , (13 , 13)))) , ((((4 , 13) , (13 , 5)) , ((13 , 13) , (4 , 4))) , (((4 , 13) , (13 , 4)) , ((13 , 13) , (4 , 5))))))
step102 : mulM matrix38 matrix1 ≡ matrix102
step102 = Eq.refl
e102 : readM w102 ≡ matrix102
e102 = Eq.trans (readM-• w38 w1) (Eq.trans (Eq.cong₂ mulM {x = readM w38} {y = matrix38} {u = readM w1} {v = matrix1} e38 e1) step102)

w103 : Word Gen
w103 = w1 • w38
matrix103 : Mat 3
matrix103 = mat ((((((4 , 13) , (12 , 4)) , ((13 , 13) , (4 , 4))) , (((13 , 4) , (4 , 13)) , ((5 , 4) , (13 , 13)))) , ((((12 , 4) , (4 , 13)) , ((4 , 4) , (13 , 13))) , (((4 , 13) , (13 , 4)) , ((13 , 13) , (5 , 4))))) , (((((13 , 5) , (4 , 13)) , ((4 , 4) , (13 , 13))) , (((13 , 4) , (4 , 13)) , ((4 , 5) , (13 , 13)))) , ((((4 , 13) , (13 , 5)) , ((13 , 13) , (4 , 4))) , (((4 , 13) , (13 , 4)) , ((13 , 13) , (4 , 5))))))
step103 : mulM matrix1 matrix38 ≡ matrix103
step103 = Eq.refl
e103 : readM w103 ≡ matrix103
e103 = Eq.trans (readM-• w1 w38) (Eq.trans (Eq.cong₂ mulM {x = readM w1} {y = matrix1} {u = readM w38} {v = matrix38} e1 e38) step103)

w104 : Word Gen
w104 = w0 • w62
matrix104 : Mat 3
matrix104 = mat ((((((5 , 4) , (4 , 13)) , ((4 , 4) , (13 , 4))) , (((4 , 5) , (4 , 13)) , ((4 , 4) , (13 , 4)))) , ((((4 , 4) , (5 , 13)) , ((4 , 4) , (13 , 4))) , (((13 , 13) , (13 , 4)) , ((13 , 13) , (5 , 13))))) , (((((4 , 4) , (4 , 13)) , ((5 , 4) , (13 , 4))) , (((4 , 4) , (4 , 13)) , ((4 , 5) , (13 , 4)))) , ((((13 , 13) , (13 , 5)) , ((13 , 13) , (4 , 13))) , (((4 , 4) , (4 , 13)) , ((4 , 4) , (13 , 5))))))
step104 : mulM matrix0 matrix62 ≡ matrix104
step104 = Eq.refl
e104 : readM w104 ≡ matrix104
e104 = Eq.trans (readM-• w0 w62) (Eq.trans (Eq.cong₂ mulM {x = readM w0} {y = matrix0} {u = readM w62} {v = matrix62} e0 e62) step104)

w105 : Word Gen
w105 = w62 • w0
matrix105 : Mat 3
matrix105 = mat ((((((5 , 4) , (4 , 13)) , ((4 , 4) , (13 , 4))) , (((4 , 5) , (4 , 13)) , ((4 , 4) , (13 , 4)))) , ((((4 , 4) , (5 , 13)) , ((4 , 4) , (13 , 4))) , (((13 , 13) , (13 , 4)) , ((13 , 13) , (5 , 13))))) , (((((4 , 4) , (4 , 13)) , ((5 , 4) , (13 , 4))) , (((4 , 4) , (4 , 13)) , ((4 , 5) , (13 , 4)))) , ((((13 , 13) , (13 , 5)) , ((13 , 13) , (4 , 13))) , (((4 , 4) , (4 , 13)) , ((4 , 4) , (13 , 5))))))
step105 : mulM matrix62 matrix0 ≡ matrix105
step105 = Eq.refl
e105 : readM w105 ≡ matrix105
e105 = Eq.trans (readM-• w62 w0) (Eq.trans (Eq.cong₂ mulM {x = readM w62} {y = matrix62} {u = readM w0} {v = matrix0} e62 e0) step105)

w106 : Word Gen
w106 = w38 • w10
matrix106 : Mat 3
matrix106 = mat ((((((13 , 4) , (5 , 13)) , ((4 , 13) , (4 , 13))) , (((4 , 13) , (13 , 5)) , ((13 , 4) , (13 , 4)))) , ((((13 , 4) , (4 , 13)) , ((4 , 13) , (5 , 13))) , (((4 , 13) , (13 , 4)) , ((13 , 4) , (13 , 5))))) , (((((4 , 12) , (13 , 4)) , ((13 , 4) , (13 , 4))) , (((12 , 4) , (4 , 13)) , ((4 , 13) , (4 , 13)))) , ((((13 , 4) , (4 , 13)) , ((5 , 13) , (4 , 13))) , (((4 , 13) , (13 , 4)) , ((13 , 5) , (13 , 4))))))
step106 : mulM matrix38 matrix10 ≡ matrix106
step106 = Eq.refl
e106 : readM w106 ≡ matrix106
e106 = Eq.trans (readM-• w38 w10) (Eq.trans (Eq.cong₂ mulM {x = readM w38} {y = matrix38} {u = readM w10} {v = matrix10} e38 e10) step106)

w107 : Word Gen
w107 = w6 • w38
matrix107 : Mat 3
matrix107 = mat ((((((13 , 4) , (5 , 13)) , ((4 , 13) , (4 , 13))) , (((4 , 13) , (13 , 5)) , ((13 , 4) , (13 , 4)))) , ((((13 , 4) , (4 , 13)) , ((4 , 13) , (5 , 13))) , (((4 , 13) , (13 , 4)) , ((13 , 4) , (13 , 5))))) , (((((4 , 12) , (13 , 4)) , ((13 , 4) , (13 , 4))) , (((12 , 4) , (4 , 13)) , ((4 , 13) , (4 , 13)))) , ((((13 , 4) , (4 , 13)) , ((5 , 13) , (4 , 13))) , (((4 , 13) , (13 , 4)) , ((13 , 5) , (13 , 4))))))
step107 : mulM matrix6 matrix38 ≡ matrix107
step107 = Eq.refl
e107 : readM w107 ≡ matrix107
e107 = Eq.trans (readM-• w6 w38) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w38} {v = matrix38} e6 e38) step107)

w108 : Word Gen
w108 = w6 • w56
matrix108 : Mat 3
matrix108 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step108 : mulM matrix6 matrix56 ≡ matrix108
step108 = Eq.refl
e108 : readM w108 ≡ matrix108
e108 = Eq.trans (readM-• w6 w56) (Eq.trans (Eq.cong₂ mulM {x = readM w6} {y = matrix6} {u = readM w56} {v = matrix56} e6 e56) step108)

w109 : Word Gen
w109 = w56 • w76
matrix109 : Mat 3
matrix109 = mat ((((((0 , 0) , (0 , 0)) , ((1 , 0) , (0 , 0))) , (((0 , 0) , (0 , 0)) , ((0 , 1) , (0 , 0)))) , ((((0 , 0) , (0 , 0)) , ((0 , 0) , (0 , 1))) , (((0 , 0) , (0 , 0)) , ((0 , 0) , (1 , 0))))) , (((((1 , 0) , (0 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 1) , (0 , 0)) , ((0 , 0) , (0 , 0)))) , ((((0 , 0) , (1 , 0)) , ((0 , 0) , (0 , 0))) , (((0 , 0) , (0 , 1)) , ((0 , 0) , (0 , 0))))))
step109 : mulM matrix56 matrix76 ≡ matrix109
step109 = Eq.refl
e109 : readM w109 ≡ matrix109
e109 = Eq.trans (readM-• w56 w76) (Eq.trans (Eq.cong₂ mulM {x = readM w56} {y = matrix56} {u = readM w76} {v = matrix76} e56 e76) step109)

w110 : Word Gen
w110 = w2 • w62
matrix110 : Mat 3
matrix110 = mat ((((((5 , 4) , (4 , 13)) , ((4 , 4) , (4 , 13))) , (((4 , 5) , (4 , 13)) , ((4 , 4) , (4 , 13)))) , ((((4 , 4) , (5 , 13)) , ((4 , 4) , (4 , 13))) , (((13 , 13) , (13 , 4)) , ((13 , 13) , (13 , 5))))) , (((((4 , 4) , (4 , 13)) , ((4 , 4) , (5 , 13))) , (((13 , 13) , (13 , 5)) , ((13 , 13) , (13 , 4)))) , ((((4 , 4) , (4 , 13)) , ((5 , 4) , (4 , 13))) , (((4 , 4) , (4 , 13)) , ((4 , 5) , (4 , 13))))))
step110 : mulM matrix2 matrix62 ≡ matrix110
step110 = Eq.refl
e110 : readM w110 ≡ matrix110
e110 = Eq.trans (readM-• w2 w62) (Eq.trans (Eq.cong₂ mulM {x = readM w2} {y = matrix2} {u = readM w62} {v = matrix62} e2 e62) step110)

w111 : Word Gen
w111 = w59 • w2
matrix111 : Mat 3
matrix111 = mat ((((((5 , 4) , (4 , 4)) , ((4 , 13) , (4 , 13))) , (((4 , 5) , (4 , 4)) , ((4 , 13) , (4 , 13)))) , ((((4 , 4) , (5 , 4)) , ((4 , 13) , (4 , 13))) , (((4 , 4) , (4 , 5)) , ((4 , 13) , (4 , 13))))) , (((((4 , 4) , (4 , 4)) , ((4 , 13) , (5 , 13))) , (((13 , 13) , (13 , 13)) , ((13 , 5) , (13 , 4)))) , ((((4 , 4) , (4 , 4)) , ((5 , 13) , (4 , 13))) , (((13 , 13) , (13 , 13)) , ((13 , 4) , (13 , 5))))))
step111 : mulM matrix59 matrix2 ≡ matrix111
step111 = Eq.refl
e111 : readM w111 ≡ matrix111
e111 = Eq.trans (readM-• w59 w2) (Eq.trans (Eq.cong₂ mulM {x = readM w59} {y = matrix59} {u = readM w2} {v = matrix2} e59 e2) step111)

