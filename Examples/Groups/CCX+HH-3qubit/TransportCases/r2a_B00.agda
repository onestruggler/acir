{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00025 ; module PE00033 ; module PE00041 ; module PE00049)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B002 using (module PE00057 ; module PE00110)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B003 using (module PE00116 ; module PE00123 ; module PE00130 ; module PE00137 ; module PE00144 ; module PE00145 ; module PE00150 ; module PE00151 ; module PE00157 ; module PE00158 ; module PE00164 ; module PE00165 ; module PE00171 ; module PE00172 ; module PE00177)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B004 using (module PE00178 ; module PE00184 ; module PE00185 ; module PE00191 ; module PE00192 ; module PE00197 ; module PE00198 ; module PE00204 ; module PE00205)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B018 using (module PE00984 ; module PE00985 ; module PE00986 ; module PE00987 ; module PE00988)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B019 using (module PE00989 ; module PE00990 ; module PE00991 ; module PE00992 ; module PE00993 ; module PE00994 ; module PE00995 ; module PE00996 ; module PE00997 ; module PE00998 ; module PE00999 ; module PE01000 ; module PE01001 ; module PE01002 ; module PE01003 ; module PE01004 ; module PE01005 ; module PE01006 ; module PE01007 ; module PE01008 ; module PE01009 ; module PE01010 ; module PE01011 ; module PE01012 ; module PE01013 ; module PE01014 ; module PE01015 ; module PE01016 ; module PE01017 ; module PE01018 ; module PE01019 ; module PE01020 ; module PE01021 ; module PE01022 ; module PE01023 ; module PE01024 ; module PE01025 ; module PE01026 ; module PE01027 ; module PE01028 ; module PE01029 ; module PE01030 ; module PE01031 ; module PE01032 ; module PE01033 ; module PE01034 ; module PE01035 ; module PE01036 ; module PE01037 ; module PE01038 ; module PE01039 ; module PE01040 ; module PE01041 ; module PE01042)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B020 using (module PE01043 ; module PE01044 ; module PE01045 ; module PE01046 ; module PE01047 ; module PE01048 ; module PE01049 ; module PE01050 ; module PE01051 ; module PE01052 ; module PE01053 ; module PE01054 ; module PE01055 ; module PE01056 ; module PE01057 ; module PE01058 ; module PE01059 ; module PE01060 ; module PE01061 ; module PE01062 ; module PE01063 ; module PE01064 ; module PE01065 ; module PE01066 ; module PE01067 ; module PE01068 ; module PE01069 ; module PE01070 ; module PE01071 ; module PE01072 ; module PE01073 ; module PE01074 ; module PE01075 ; module PE01076 ; module PE01077 ; module PE01078 ; module PE01079 ; module PE01080 ; module PE01081 ; module PE01082 ; module PE01083)

module r2a_ij0123 where

  proved : X01 • X23 ≈ X23 • X01
  proved = by-assoc-and PE00110.proved Eq.refl Eq.refl

module r2a_ij0124 where

  proved : X01 • X24 ≈ X24 • X01
  proved = by-assoc-and PE00116.proved Eq.refl Eq.refl

module r2a_ij0125 where

  proved : X01 • X25 ≈ X25 • X01
  proved = by-assoc-and PE00123.proved Eq.refl Eq.refl

module r2a_ij0126 where

  proved : X01 • X26 ≈ X26 • X01
  proved = by-assoc-and PE00130.proved Eq.refl Eq.refl

module r2a_ij0127 where

  proved : X01 • X27 ≈ X27 • X01
  proved = by-assoc-and PE00137.proved Eq.refl Eq.refl

module r2a_ij0134 where

  proved : X01 • X34 ≈ X34 • X01
  proved = by-assoc-and PE00144.proved Eq.refl Eq.refl

module r2a_ij0135 where

  proved : X01 • X35 ≈ X35 • X01
  proved = by-assoc-and PE00150.proved Eq.refl Eq.refl

module r2a_ij0136 where

  proved : X01 • X36 ≈ X36 • X01
  proved = by-assoc-and PE00157.proved Eq.refl Eq.refl

module r2a_ij0137 where

  proved : X01 • X37 ≈ X37 • X01
  proved = by-assoc-and PE00164.proved Eq.refl Eq.refl

module r2a_ij0145 where

  proved : X01 • X45 ≈ X45 • X01
  proved = by-assoc-and PE00171.proved Eq.refl Eq.refl

module r2a_ij0146 where

  proved : X01 • X46 ≈ X46 • X01
  proved = by-assoc-and PE00177.proved Eq.refl Eq.refl

module r2a_ij0147 where

  proved : X01 • X47 ≈ X47 • X01
  proved = by-assoc-and PE00184.proved Eq.refl Eq.refl

module r2a_ij0156 where

  proved : X01 • X56 ≈ X56 • X01
  proved = by-assoc-and PE00191.proved Eq.refl Eq.refl

module r2a_ij0157 where

  proved : X01 • X57 ≈ X57 • X01
  proved = by-assoc-and PE00197.proved Eq.refl Eq.refl

module r2a_ij0167 where

  proved : X01 • X67 ≈ X67 • X01
  proved = by-assoc-and PE00204.proved Eq.refl Eq.refl

module r2a_ij0213 where

  proved : X02 • X13 ≈ X13 • X02
  proved = by-assoc-and PE00984.proved Eq.refl Eq.refl

module r2a_ij0214 where

  proved : X02 • X14 ≈ X14 • X02
  proved = by-assoc-and PE00985.proved Eq.refl Eq.refl

module r2a_ij0215 where

  proved : X02 • X15 ≈ X15 • X02
  proved = by-assoc-and PE00986.proved Eq.refl Eq.refl

module r2a_ij0216 where

  proved : X02 • X16 ≈ X16 • X02
  proved = by-assoc-and PE00987.proved Eq.refl Eq.refl

module r2a_ij0217 where

  proved : X02 • X17 ≈ X17 • X02
  proved = by-assoc-and PE00988.proved Eq.refl Eq.refl

module r2a_ij0234 where

  proved : X02 • X34 ≈ X34 • X02
  proved = by-assoc-and PE00989.proved Eq.refl Eq.refl

module r2a_ij0235 where

  proved : X02 • X35 ≈ X35 • X02
  proved = by-assoc-and PE00990.proved Eq.refl Eq.refl

module r2a_ij0236 where

  proved : X02 • X36 ≈ X36 • X02
  proved = by-assoc-and PE00991.proved Eq.refl Eq.refl

module r2a_ij0237 where

  proved : X02 • X37 ≈ X37 • X02
  proved = by-assoc-and PE00992.proved Eq.refl Eq.refl

module r2a_ij0245 where

  proved : X02 • X45 ≈ X45 • X02
  proved = by-assoc-and PE00993.proved Eq.refl Eq.refl

module r2a_ij0246 where

  proved : X02 • X46 ≈ X46 • X02
  proved = by-assoc-and PE00994.proved Eq.refl Eq.refl

module r2a_ij0247 where

  proved : X02 • X47 ≈ X47 • X02
  proved = by-assoc-and PE00995.proved Eq.refl Eq.refl

module r2a_ij0256 where

  proved : X02 • X56 ≈ X56 • X02
  proved = by-assoc-and PE00996.proved Eq.refl Eq.refl

module r2a_ij0257 where

  proved : X02 • X57 ≈ X57 • X02
  proved = by-assoc-and PE00997.proved Eq.refl Eq.refl

module r2a_ij0267 where

  proved : X02 • X67 ≈ X67 • X02
  proved = by-assoc-and PE00998.proved Eq.refl Eq.refl

module r2a_ij0312 where

  proved : X03 • X12 ≈ X12 • X03
  proved = by-assoc-and PE00999.proved Eq.refl Eq.refl

module r2a_ij0314 where

  proved : X03 • X14 ≈ X14 • X03
  proved = by-assoc-and PE01000.proved Eq.refl Eq.refl

module r2a_ij0315 where

  proved : X03 • X15 ≈ X15 • X03
  proved = by-assoc-and PE01001.proved Eq.refl Eq.refl

module r2a_ij0316 where

  proved : X03 • X16 ≈ X16 • X03
  proved = by-assoc-and PE01002.proved Eq.refl Eq.refl

module r2a_ij0317 where

  proved : X03 • X17 ≈ X17 • X03
  proved = by-assoc-and PE01003.proved Eq.refl Eq.refl

module r2a_ij0324 where

  proved : X03 • X24 ≈ X24 • X03
  proved = by-assoc-and PE01004.proved Eq.refl Eq.refl

module r2a_ij0325 where

  proved : X03 • X25 ≈ X25 • X03
  proved = by-assoc-and PE01005.proved Eq.refl Eq.refl

module r2a_ij0326 where

  proved : X03 • X26 ≈ X26 • X03
  proved = by-assoc-and PE01006.proved Eq.refl Eq.refl

module r2a_ij0327 where

  proved : X03 • X27 ≈ X27 • X03
  proved = by-assoc-and PE01007.proved Eq.refl Eq.refl

module r2a_ij0345 where

  proved : X03 • X45 ≈ X45 • X03
  proved = by-assoc-and PE01008.proved Eq.refl Eq.refl

module r2a_ij0346 where

  proved : X03 • X46 ≈ X46 • X03
  proved = by-assoc-and PE01009.proved Eq.refl Eq.refl

module r2a_ij0347 where

  proved : X03 • X47 ≈ X47 • X03
  proved = by-assoc-and PE01010.proved Eq.refl Eq.refl

module r2a_ij0356 where

  proved : X03 • X56 ≈ X56 • X03
  proved = by-assoc-and PE01011.proved Eq.refl Eq.refl

module r2a_ij0357 where

  proved : X03 • X57 ≈ X57 • X03
  proved = by-assoc-and PE01012.proved Eq.refl Eq.refl

module r2a_ij0367 where

  proved : X03 • X67 ≈ X67 • X03
  proved = by-assoc-and PE01013.proved Eq.refl Eq.refl

module r2a_ij0412 where

  proved : X04 • X12 ≈ X12 • X04
  proved = by-assoc-and PE01014.proved Eq.refl Eq.refl

module r2a_ij0413 where

  proved : X04 • X13 ≈ X13 • X04
  proved = by-assoc-and PE01015.proved Eq.refl Eq.refl

module r2a_ij0415 where

  proved : X04 • X15 ≈ X15 • X04
  proved = by-assoc-and PE01016.proved Eq.refl Eq.refl

module r2a_ij0416 where

  proved : X04 • X16 ≈ X16 • X04
  proved = by-assoc-and PE01017.proved Eq.refl Eq.refl

module r2a_ij0417 where

  proved : X04 • X17 ≈ X17 • X04
  proved = by-assoc-and PE01018.proved Eq.refl Eq.refl

module r2a_ij0423 where

  proved : X04 • X23 ≈ X23 • X04
  proved = by-assoc-and PE01019.proved Eq.refl Eq.refl

module r2a_ij0425 where

  proved : X04 • X25 ≈ X25 • X04
  proved = by-assoc-and PE01020.proved Eq.refl Eq.refl

module r2a_ij0426 where

  proved : X04 • X26 ≈ X26 • X04
  proved = by-assoc-and PE01021.proved Eq.refl Eq.refl

module r2a_ij0427 where

  proved : X04 • X27 ≈ X27 • X04
  proved = by-assoc-and PE01022.proved Eq.refl Eq.refl

module r2a_ij0435 where

  proved : X04 • X35 ≈ X35 • X04
  proved = by-assoc-and PE01023.proved Eq.refl Eq.refl

module r2a_ij0436 where

  proved : X04 • X36 ≈ X36 • X04
  proved = by-assoc-and PE01024.proved Eq.refl Eq.refl

module r2a_ij0437 where

  proved : X04 • X37 ≈ X37 • X04
  proved = by-assoc-and PE01025.proved Eq.refl Eq.refl

module r2a_ij0456 where

  proved : X04 • X56 ≈ X56 • X04
  proved = by-assoc-and PE01026.proved Eq.refl Eq.refl

module r2a_ij0457 where

  proved : X04 • X57 ≈ X57 • X04
  proved = by-assoc-and PE01027.proved Eq.refl Eq.refl

module r2a_ij0467 where

  proved : X04 • X67 ≈ X67 • X04
  proved = by-assoc-and PE01028.proved Eq.refl Eq.refl

module r2a_ij0512 where

  proved : X05 • X12 ≈ X12 • X05
  proved = by-assoc-and PE01029.proved Eq.refl Eq.refl

module r2a_ij0513 where

  proved : X05 • X13 ≈ X13 • X05
  proved = by-assoc-and PE01030.proved Eq.refl Eq.refl

module r2a_ij0514 where

  proved : X05 • X14 ≈ X14 • X05
  proved = by-assoc-and PE01031.proved Eq.refl Eq.refl

module r2a_ij0516 where

  proved : X05 • X16 ≈ X16 • X05
  proved = by-assoc-and PE01032.proved Eq.refl Eq.refl

module r2a_ij0517 where

  proved : X05 • X17 ≈ X17 • X05
  proved = by-assoc-and PE01033.proved Eq.refl Eq.refl

module r2a_ij0523 where

  proved : X05 • X23 ≈ X23 • X05
  proved = by-assoc-and PE01034.proved Eq.refl Eq.refl

module r2a_ij0524 where

  proved : X05 • X24 ≈ X24 • X05
  proved = by-assoc-and PE01035.proved Eq.refl Eq.refl

module r2a_ij0526 where

  proved : X05 • X26 ≈ X26 • X05
  proved = by-assoc-and PE01036.proved Eq.refl Eq.refl

module r2a_ij0527 where

  proved : X05 • X27 ≈ X27 • X05
  proved = by-assoc-and PE01037.proved Eq.refl Eq.refl

module r2a_ij0534 where

  proved : X05 • X34 ≈ X34 • X05
  proved = by-assoc-and PE01038.proved Eq.refl Eq.refl

module r2a_ij0536 where

  proved : X05 • X36 ≈ X36 • X05
  proved = by-assoc-and PE01039.proved Eq.refl Eq.refl

module r2a_ij0537 where

  proved : X05 • X37 ≈ X37 • X05
  proved = by-assoc-and PE01040.proved Eq.refl Eq.refl

module r2a_ij0546 where

  proved : X05 • X46 ≈ X46 • X05
  proved = by-assoc-and PE01041.proved Eq.refl Eq.refl

module r2a_ij0547 where

  proved : X05 • X47 ≈ X47 • X05
  proved = by-assoc-and PE01042.proved Eq.refl Eq.refl

module r2a_ij0567 where

  proved : X05 • X67 ≈ X67 • X05
  proved = by-assoc-and PE01043.proved Eq.refl Eq.refl

module r2a_ij0612 where

  proved : X06 • X12 ≈ X12 • X06
  proved = by-assoc-and PE01044.proved Eq.refl Eq.refl

module r2a_ij0613 where

  proved : X06 • X13 ≈ X13 • X06
  proved = by-assoc-and PE01045.proved Eq.refl Eq.refl

module r2a_ij0614 where

  proved : X06 • X14 ≈ X14 • X06
  proved = by-assoc-and PE01046.proved Eq.refl Eq.refl

module r2a_ij0615 where

  proved : X06 • X15 ≈ X15 • X06
  proved = by-assoc-and PE01047.proved Eq.refl Eq.refl

module r2a_ij0617 where

  proved : X06 • X17 ≈ X17 • X06
  proved = by-assoc-and PE01048.proved Eq.refl Eq.refl

module r2a_ij0623 where

  proved : X06 • X23 ≈ X23 • X06
  proved = by-assoc-and PE01049.proved Eq.refl Eq.refl

module r2a_ij0624 where

  proved : X06 • X24 ≈ X24 • X06
  proved = by-assoc-and PE01050.proved Eq.refl Eq.refl

module r2a_ij0625 where

  proved : X06 • X25 ≈ X25 • X06
  proved = by-assoc-and PE01051.proved Eq.refl Eq.refl

module r2a_ij0627 where

  proved : X06 • X27 ≈ X27 • X06
  proved = by-assoc-and PE01052.proved Eq.refl Eq.refl

module r2a_ij0634 where

  proved : X06 • X34 ≈ X34 • X06
  proved = by-assoc-and PE01053.proved Eq.refl Eq.refl

module r2a_ij0635 where

  proved : X06 • X35 ≈ X35 • X06
  proved = by-assoc-and PE01054.proved Eq.refl Eq.refl

module r2a_ij0637 where

  proved : X06 • X37 ≈ X37 • X06
  proved = by-assoc-and PE01055.proved Eq.refl Eq.refl

module r2a_ij0645 where

  proved : X06 • X45 ≈ X45 • X06
  proved = by-assoc-and PE01056.proved Eq.refl Eq.refl

module r2a_ij0647 where

  proved : X06 • X47 ≈ X47 • X06
  proved = by-assoc-and PE01057.proved Eq.refl Eq.refl

module r2a_ij0657 where

  proved : X06 • X57 ≈ X57 • X06
  proved = by-assoc-and PE01058.proved Eq.refl Eq.refl

module r2a_ij0712 where

  proved : X07 • X12 ≈ X12 • X07
  proved = by-assoc-and PE01059.proved Eq.refl Eq.refl

module r2a_ij0713 where

  proved : X07 • X13 ≈ X13 • X07
  proved = by-assoc-and PE01060.proved Eq.refl Eq.refl

module r2a_ij0714 where

  proved : X07 • X14 ≈ X14 • X07
  proved = by-assoc-and PE01061.proved Eq.refl Eq.refl

module r2a_ij0715 where

  proved : X07 • X15 ≈ X15 • X07
  proved = by-assoc-and PE01062.proved Eq.refl Eq.refl

module r2a_ij0716 where

  proved : X07 • X16 ≈ X16 • X07
  proved = by-assoc-and PE01063.proved Eq.refl Eq.refl

module r2a_ij0723 where

  proved : X07 • X23 ≈ X23 • X07
  proved = by-assoc-and PE01064.proved Eq.refl Eq.refl

module r2a_ij0724 where

  proved : X07 • X24 ≈ X24 • X07
  proved = by-assoc-and PE01065.proved Eq.refl Eq.refl

module r2a_ij0725 where

  proved : X07 • X25 ≈ X25 • X07
  proved = by-assoc-and PE01066.proved Eq.refl Eq.refl

module r2a_ij0726 where

  proved : X07 • X26 ≈ X26 • X07
  proved = by-assoc-and PE01067.proved Eq.refl Eq.refl

module r2a_ij0734 where

  proved : X07 • X34 ≈ X34 • X07
  proved = by-assoc-and PE01068.proved Eq.refl Eq.refl

module r2a_ij0735 where

  proved : X07 • X35 ≈ X35 • X07
  proved = by-assoc-and PE01069.proved Eq.refl Eq.refl

module r2a_ij0736 where

  proved : X07 • X36 ≈ X36 • X07
  proved = by-assoc-and PE01070.proved Eq.refl Eq.refl

module r2a_ij0745 where

  proved : X07 • X45 ≈ X45 • X07
  proved = by-assoc-and PE01071.proved Eq.refl Eq.refl

module r2a_ij0746 where

  proved : X07 • X46 ≈ X46 • X07
  proved = by-assoc-and PE01072.proved Eq.refl Eq.refl

module r2a_ij0756 where

  proved : X07 • X56 ≈ X56 • X07
  proved = by-assoc-and PE01073.proved Eq.refl Eq.refl

module r2a_ij1203 where

  proved : X12 • X03 ≈ X03 • X12
  proved = by-assoc-and PE00025.proved Eq.refl Eq.refl

module r2a_ij1204 where

  proved : X12 • X04 ≈ X04 • X12
  proved = by-assoc-and PE00033.proved Eq.refl Eq.refl

module r2a_ij1205 where

  proved : X12 • X05 ≈ X05 • X12
  proved = by-assoc-and PE00041.proved Eq.refl Eq.refl

module r2a_ij1206 where

  proved : X12 • X06 ≈ X06 • X12
  proved = by-assoc-and PE00049.proved Eq.refl Eq.refl

module r2a_ij1207 where

  proved : X12 • X07 ≈ X07 • X12
  proved = by-assoc-and PE00057.proved Eq.refl Eq.refl

module r2a_ij1234 where

  proved : X12 • X34 ≈ X34 • X12
  proved = by-assoc-and PE00145.proved Eq.refl Eq.refl

module r2a_ij1235 where

  proved : X12 • X35 ≈ X35 • X12
  proved = by-assoc-and PE00151.proved Eq.refl Eq.refl

module r2a_ij1236 where

  proved : X12 • X36 ≈ X36 • X12
  proved = by-assoc-and PE00158.proved Eq.refl Eq.refl

module r2a_ij1237 where

  proved : X12 • X37 ≈ X37 • X12
  proved = by-assoc-and PE00165.proved Eq.refl Eq.refl

module r2a_ij1245 where

  proved : X12 • X45 ≈ X45 • X12
  proved = by-assoc-and PE00172.proved Eq.refl Eq.refl

module r2a_ij1246 where

  proved : X12 • X46 ≈ X46 • X12
  proved = by-assoc-and PE00178.proved Eq.refl Eq.refl

module r2a_ij1247 where

  proved : X12 • X47 ≈ X47 • X12
  proved = by-assoc-and PE00185.proved Eq.refl Eq.refl

module r2a_ij1256 where

  proved : X12 • X56 ≈ X56 • X12
  proved = by-assoc-and PE00192.proved Eq.refl Eq.refl

module r2a_ij1257 where

  proved : X12 • X57 ≈ X57 • X12
  proved = by-assoc-and PE00198.proved Eq.refl Eq.refl

module r2a_ij1267 where

  proved : X12 • X67 ≈ X67 • X12
  proved = by-assoc-and PE00205.proved Eq.refl Eq.refl

module r2a_ij1302 where

  proved : X13 • X02 ≈ X02 • X13
  proved = by-assoc-and PE01074.proved Eq.refl Eq.refl

module r2a_ij1304 where

  proved : X13 • X04 ≈ X04 • X13
  proved = by-assoc-and PE01075.proved Eq.refl Eq.refl

module r2a_ij1305 where

  proved : X13 • X05 ≈ X05 • X13
  proved = by-assoc-and PE01076.proved Eq.refl Eq.refl

module r2a_ij1306 where

  proved : X13 • X06 ≈ X06 • X13
  proved = by-assoc-and PE01077.proved Eq.refl Eq.refl

module r2a_ij1307 where

  proved : X13 • X07 ≈ X07 • X13
  proved = by-assoc-and PE01078.proved Eq.refl Eq.refl

module r2a_ij1324 where

  proved : X13 • X24 ≈ X24 • X13
  proved = by-assoc-and PE01079.proved Eq.refl Eq.refl

module r2a_ij1325 where

  proved : X13 • X25 ≈ X25 • X13
  proved = by-assoc-and PE01080.proved Eq.refl Eq.refl

module r2a_ij1326 where

  proved : X13 • X26 ≈ X26 • X13
  proved = by-assoc-and PE01081.proved Eq.refl Eq.refl

module r2a_ij1327 where

  proved : X13 • X27 ≈ X27 • X13
  proved = by-assoc-and PE01082.proved Eq.refl Eq.refl

module r2a_ij1345 where

  proved : X13 • X45 ≈ X45 • X13
  proved = by-assoc-and PE01083.proved Eq.refl Eq.refl
