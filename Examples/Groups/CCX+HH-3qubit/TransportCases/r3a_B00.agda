{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B002 using (module PE00063 ; module PE00064 ; module PE00065 ; module PE00066 ; module PE00067 ; module PE00068 ; module PE00076 ; module PE00083 ; module PE00090 ; module PE00097 ; module PE00104)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B003 using (module PE00118 ; module PE00125 ; module PE00132 ; module PE00139 ; module PE00153 ; module PE00160 ; module PE00167)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B004 using (module PE00181 ; module PE00188 ; module PE00202)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B024 using (module PE01301 ; module PE01302 ; module PE01303 ; module PE01304 ; module PE01305 ; module PE01306 ; module PE01307 ; module PE01308 ; module PE01309 ; module PE01310 ; module PE01311)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B025 using (module PE01312 ; module PE01313 ; module PE01314 ; module PE01315 ; module PE01316 ; module PE01317 ; module PE01318 ; module PE01319 ; module PE01320 ; module PE01321 ; module PE01322 ; module PE01323 ; module PE01324 ; module PE01325 ; module PE01326 ; module PE01327 ; module PE01328 ; module PE01329 ; module PE01330 ; module PE01331 ; module PE01332 ; module PE01333 ; module PE01334 ; module PE01335)

module r3a_ij012 where

  proved : X01 • X02 ≈ X12 • X01
  proved = by-assoc-and PE00063.proved Eq.refl Eq.refl

module r3a_ij013 where

  proved : X01 • X03 ≈ X13 • X01
  proved = by-assoc-and PE00064.proved Eq.refl Eq.refl

module r3a_ij014 where

  proved : X01 • X04 ≈ X14 • X01
  proved = by-assoc-and PE00065.proved Eq.refl Eq.refl

module r3a_ij015 where

  proved : X01 • X05 ≈ X15 • X01
  proved = by-assoc-and PE00066.proved Eq.refl Eq.refl

module r3a_ij016 where

  proved : X01 • X06 ≈ X16 • X01
  proved = by-assoc-and PE00067.proved Eq.refl Eq.refl

module r3a_ij017 where

  proved : X01 • X07 ≈ X17 • X01
  proved = by-assoc-and PE00068.proved Eq.refl Eq.refl

module r3a_ij023 where

  proved : X02 • X03 ≈ X23 • X02
  proved = by-assoc-and PE01301.proved Eq.refl Eq.refl

module r3a_ij024 where

  proved : X02 • X04 ≈ X24 • X02
  proved = by-assoc-and PE01302.proved Eq.refl Eq.refl

module r3a_ij025 where

  proved : X02 • X05 ≈ X25 • X02
  proved = by-assoc-and PE01303.proved Eq.refl Eq.refl

module r3a_ij026 where

  proved : X02 • X06 ≈ X26 • X02
  proved = by-assoc-and PE01304.proved Eq.refl Eq.refl

module r3a_ij027 where

  proved : X02 • X07 ≈ X27 • X02
  proved = by-assoc-and PE01305.proved Eq.refl Eq.refl

module r3a_ij034 where

  proved : X03 • X04 ≈ X34 • X03
  proved = by-assoc-and PE01306.proved Eq.refl Eq.refl

module r3a_ij035 where

  proved : X03 • X05 ≈ X35 • X03
  proved = by-assoc-and PE01307.proved Eq.refl Eq.refl

module r3a_ij036 where

  proved : X03 • X06 ≈ X36 • X03
  proved = by-assoc-and PE01308.proved Eq.refl Eq.refl

module r3a_ij037 where

  proved : X03 • X07 ≈ X37 • X03
  proved = by-assoc-and PE01309.proved Eq.refl Eq.refl

module r3a_ij045 where

  proved : X04 • X05 ≈ X45 • X04
  proved = by-assoc-and PE01310.proved Eq.refl Eq.refl

module r3a_ij046 where

  proved : X04 • X06 ≈ X46 • X04
  proved = by-assoc-and PE01311.proved Eq.refl Eq.refl

module r3a_ij047 where

  proved : X04 • X07 ≈ X47 • X04
  proved = by-assoc-and PE01312.proved Eq.refl Eq.refl

module r3a_ij056 where

  proved : X05 • X06 ≈ X56 • X05
  proved = by-assoc-and PE01313.proved Eq.refl Eq.refl

module r3a_ij057 where

  proved : X05 • X07 ≈ X57 • X05
  proved = by-assoc-and PE01314.proved Eq.refl Eq.refl

module r3a_ij067 where

  proved : X06 • X07 ≈ X67 • X06
  proved = by-assoc-and PE01315.proved Eq.refl Eq.refl

module r3a_ij123 where

  proved : X12 • X13 ≈ X23 • X12
  proved = by-assoc-and PE00076.proved Eq.refl Eq.refl

module r3a_ij124 where

  proved : X12 • X14 ≈ X24 • X12
  proved = by-assoc-and PE00083.proved Eq.refl Eq.refl

module r3a_ij125 where

  proved : X12 • X15 ≈ X25 • X12
  proved = by-assoc-and PE00090.proved Eq.refl Eq.refl

module r3a_ij126 where

  proved : X12 • X16 ≈ X26 • X12
  proved = by-assoc-and PE00097.proved Eq.refl Eq.refl

module r3a_ij127 where

  proved : X12 • X17 ≈ X27 • X12
  proved = by-assoc-and PE00104.proved Eq.refl Eq.refl

module r3a_ij134 where

  proved : X13 • X14 ≈ X34 • X13
  proved = by-assoc-and PE01316.proved Eq.refl Eq.refl

module r3a_ij135 where

  proved : X13 • X15 ≈ X35 • X13
  proved = by-assoc-and PE01317.proved Eq.refl Eq.refl

module r3a_ij136 where

  proved : X13 • X16 ≈ X36 • X13
  proved = by-assoc-and PE01318.proved Eq.refl Eq.refl

module r3a_ij137 where

  proved : X13 • X17 ≈ X37 • X13
  proved = by-assoc-and PE01319.proved Eq.refl Eq.refl

module r3a_ij145 where

  proved : X14 • X15 ≈ X45 • X14
  proved = by-assoc-and PE01320.proved Eq.refl Eq.refl

module r3a_ij146 where

  proved : X14 • X16 ≈ X46 • X14
  proved = by-assoc-and PE01321.proved Eq.refl Eq.refl

module r3a_ij147 where

  proved : X14 • X17 ≈ X47 • X14
  proved = by-assoc-and PE01322.proved Eq.refl Eq.refl

module r3a_ij156 where

  proved : X15 • X16 ≈ X56 • X15
  proved = by-assoc-and PE01323.proved Eq.refl Eq.refl

module r3a_ij157 where

  proved : X15 • X17 ≈ X57 • X15
  proved = by-assoc-and PE01324.proved Eq.refl Eq.refl

module r3a_ij167 where

  proved : X16 • X17 ≈ X67 • X16
  proved = by-assoc-and PE01325.proved Eq.refl Eq.refl

module r3a_ij234 where

  proved : X23 • X24 ≈ X34 • X23
  proved = by-assoc-and PE00118.proved Eq.refl Eq.refl

module r3a_ij235 where

  proved : X23 • X25 ≈ X35 • X23
  proved = by-assoc-and PE00125.proved Eq.refl Eq.refl

module r3a_ij236 where

  proved : X23 • X26 ≈ X36 • X23
  proved = by-assoc-and PE00132.proved Eq.refl Eq.refl

module r3a_ij237 where

  proved : X23 • X27 ≈ X37 • X23
  proved = by-assoc-and PE00139.proved Eq.refl Eq.refl

module r3a_ij245 where

  proved : X24 • X25 ≈ X45 • X24
  proved = by-assoc-and PE01326.proved Eq.refl Eq.refl

module r3a_ij246 where

  proved : X24 • X26 ≈ X46 • X24
  proved = by-assoc-and PE01327.proved Eq.refl Eq.refl

module r3a_ij247 where

  proved : X24 • X27 ≈ X47 • X24
  proved = by-assoc-and PE01328.proved Eq.refl Eq.refl

module r3a_ij256 where

  proved : X25 • X26 ≈ X56 • X25
  proved = by-assoc-and PE01329.proved Eq.refl Eq.refl

module r3a_ij257 where

  proved : X25 • X27 ≈ X57 • X25
  proved = by-assoc-and PE01330.proved Eq.refl Eq.refl

module r3a_ij267 where

  proved : X26 • X27 ≈ X67 • X26
  proved = by-assoc-and PE01331.proved Eq.refl Eq.refl

module r3a_ij345 where

  proved : X34 • X35 ≈ X45 • X34
  proved = by-assoc-and PE00153.proved Eq.refl Eq.refl

module r3a_ij346 where

  proved : X34 • X36 ≈ X46 • X34
  proved = by-assoc-and PE00160.proved Eq.refl Eq.refl

module r3a_ij347 where

  proved : X34 • X37 ≈ X47 • X34
  proved = by-assoc-and PE00167.proved Eq.refl Eq.refl

module r3a_ij356 where

  proved : X35 • X36 ≈ X56 • X35
  proved = by-assoc-and PE01332.proved Eq.refl Eq.refl

module r3a_ij357 where

  proved : X35 • X37 ≈ X57 • X35
  proved = by-assoc-and PE01333.proved Eq.refl Eq.refl

module r3a_ij367 where

  proved : X36 • X37 ≈ X67 • X36
  proved = by-assoc-and PE01334.proved Eq.refl Eq.refl

module r3a_ij456 where

  proved : X45 • X46 ≈ X56 • X45
  proved = by-assoc-and PE00181.proved Eq.refl Eq.refl

module r3a_ij457 where

  proved : X45 • X47 ≈ X57 • X45
  proved = by-assoc-and PE00188.proved Eq.refl Eq.refl

module r3a_ij467 where

  proved : X46 • X47 ≈ X67 • X46
  proved = by-assoc-and PE01335.proved Eq.refl Eq.refl

module r3a_ij567 where

  proved : X56 • X57 ≈ X67 • X56
  proved = by-assoc-and PE00202.proved Eq.refl Eq.refl
