{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00147 ; module PE00155 ; module PE00163)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00009 ; module PE00018 ; module PE00027 ; module PE00036 ; module PE00045)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B002 using (module PE00054 ; module PE00070 ; module PE00078 ; module PE00086 ; module PE00094 ; module PE00102)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B003 using (module PE00112 ; module PE00120 ; module PE00128 ; module PE00136 ; module PE00175)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B004 using (module PE00183 ; module PE00196)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B025 using (module PE01336 ; module PE01337 ; module PE01338 ; module PE01339 ; module PE01340 ; module PE01341 ; module PE01342 ; module PE01343 ; module PE01344 ; module PE01345 ; module PE01346 ; module PE01347 ; module PE01348 ; module PE01349 ; module PE01350 ; module PE01351 ; module PE01352 ; module PE01353 ; module PE01354 ; module PE01355 ; module PE01356 ; module PE01357 ; module PE01358 ; module PE01359 ; module PE01360 ; module PE01361 ; module PE01362 ; module PE01363 ; module PE01364 ; module PE01365)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B026 using (module PE01366 ; module PE01367 ; module PE01368 ; module PE01369 ; module PE01370)

module r3b_ij012 where

  proved : X12 • X01 ≈ X02 • X12
  proved = by-assoc-and PE00009.proved Eq.refl Eq.refl

module r3b_ij013 where

  proved : X13 • X01 ≈ X03 • X13
  proved = by-assoc-and PE01336.proved Eq.refl Eq.refl

module r3b_ij014 where

  proved : X14 • X01 ≈ X04 • X14
  proved = by-assoc-and PE01337.proved Eq.refl Eq.refl

module r3b_ij015 where

  proved : X15 • X01 ≈ X05 • X15
  proved = by-assoc-and PE01338.proved Eq.refl Eq.refl

module r3b_ij016 where

  proved : X16 • X01 ≈ X06 • X16
  proved = by-assoc-and PE01339.proved Eq.refl Eq.refl

module r3b_ij017 where

  proved : X17 • X01 ≈ X07 • X17
  proved = by-assoc-and PE01340.proved Eq.refl Eq.refl

module r3b_ij023 where

  proved : X23 • X02 ≈ X03 • X23
  proved = by-assoc-and PE00018.proved Eq.refl Eq.refl

module r3b_ij024 where

  proved : X24 • X02 ≈ X04 • X24
  proved = by-assoc-and PE01341.proved Eq.refl Eq.refl

module r3b_ij025 where

  proved : X25 • X02 ≈ X05 • X25
  proved = by-assoc-and PE01342.proved Eq.refl Eq.refl

module r3b_ij026 where

  proved : X26 • X02 ≈ X06 • X26
  proved = by-assoc-and PE01343.proved Eq.refl Eq.refl

module r3b_ij027 where

  proved : X27 • X02 ≈ X07 • X27
  proved = by-assoc-and PE01344.proved Eq.refl Eq.refl

module r3b_ij034 where

  proved : X34 • X03 ≈ X04 • X34
  proved = by-assoc-and PE00027.proved Eq.refl Eq.refl

module r3b_ij035 where

  proved : X35 • X03 ≈ X05 • X35
  proved = by-assoc-and PE01345.proved Eq.refl Eq.refl

module r3b_ij036 where

  proved : X36 • X03 ≈ X06 • X36
  proved = by-assoc-and PE01346.proved Eq.refl Eq.refl

module r3b_ij037 where

  proved : X37 • X03 ≈ X07 • X37
  proved = by-assoc-and PE01347.proved Eq.refl Eq.refl

module r3b_ij045 where

  proved : X45 • X04 ≈ X05 • X45
  proved = by-assoc-and PE00036.proved Eq.refl Eq.refl

module r3b_ij046 where

  proved : X46 • X04 ≈ X06 • X46
  proved = by-assoc-and PE01348.proved Eq.refl Eq.refl

module r3b_ij047 where

  proved : X47 • X04 ≈ X07 • X47
  proved = by-assoc-and PE01349.proved Eq.refl Eq.refl

module r3b_ij056 where

  proved : X56 • X05 ≈ X06 • X56
  proved = by-assoc-and PE00045.proved Eq.refl Eq.refl

module r3b_ij057 where

  proved : X57 • X05 ≈ X07 • X57
  proved = by-assoc-and PE01350.proved Eq.refl Eq.refl

module r3b_ij067 where

  proved : X67 • X06 ≈ X07 • X67
  proved = by-assoc-and PE00054.proved Eq.refl Eq.refl

module r3b_ij123 where

  proved : X23 • X12 ≈ X13 • X23
  proved = by-assoc-and PE00070.proved Eq.refl Eq.refl

module r3b_ij124 where

  proved : X24 • X12 ≈ X14 • X24
  proved = by-assoc-and PE01351.proved Eq.refl Eq.refl

module r3b_ij125 where

  proved : X25 • X12 ≈ X15 • X25
  proved = by-assoc-and PE01352.proved Eq.refl Eq.refl

module r3b_ij126 where

  proved : X26 • X12 ≈ X16 • X26
  proved = by-assoc-and PE01353.proved Eq.refl Eq.refl

module r3b_ij127 where

  proved : X27 • X12 ≈ X17 • X27
  proved = by-assoc-and PE01354.proved Eq.refl Eq.refl

module r3b_ij134 where

  proved : X34 • X13 ≈ X14 • X34
  proved = by-assoc-and PE00078.proved Eq.refl Eq.refl

module r3b_ij135 where

  proved : X35 • X13 ≈ X15 • X35
  proved = by-assoc-and PE01355.proved Eq.refl Eq.refl

module r3b_ij136 where

  proved : X36 • X13 ≈ X16 • X36
  proved = by-assoc-and PE01356.proved Eq.refl Eq.refl

module r3b_ij137 where

  proved : X37 • X13 ≈ X17 • X37
  proved = by-assoc-and PE01357.proved Eq.refl Eq.refl

module r3b_ij145 where

  proved : X45 • X14 ≈ X15 • X45
  proved = by-assoc-and PE00086.proved Eq.refl Eq.refl

module r3b_ij146 where

  proved : X46 • X14 ≈ X16 • X46
  proved = by-assoc-and PE01358.proved Eq.refl Eq.refl

module r3b_ij147 where

  proved : X47 • X14 ≈ X17 • X47
  proved = by-assoc-and PE01359.proved Eq.refl Eq.refl

module r3b_ij156 where

  proved : X56 • X15 ≈ X16 • X56
  proved = by-assoc-and PE00094.proved Eq.refl Eq.refl

module r3b_ij157 where

  proved : X57 • X15 ≈ X17 • X57
  proved = by-assoc-and PE01360.proved Eq.refl Eq.refl

module r3b_ij167 where

  proved : X67 • X16 ≈ X17 • X67
  proved = by-assoc-and PE00102.proved Eq.refl Eq.refl

module r3b_ij234 where

  proved : X34 • X23 ≈ X24 • X34
  proved = by-assoc-and PE00112.proved Eq.refl Eq.refl

module r3b_ij235 where

  proved : X35 • X23 ≈ X25 • X35
  proved = by-assoc-and PE01361.proved Eq.refl Eq.refl

module r3b_ij236 where

  proved : X36 • X23 ≈ X26 • X36
  proved = by-assoc-and PE01362.proved Eq.refl Eq.refl

module r3b_ij237 where

  proved : X37 • X23 ≈ X27 • X37
  proved = by-assoc-and PE01363.proved Eq.refl Eq.refl

module r3b_ij245 where

  proved : X45 • X24 ≈ X25 • X45
  proved = by-assoc-and PE00120.proved Eq.refl Eq.refl

module r3b_ij246 where

  proved : X46 • X24 ≈ X26 • X46
  proved = by-assoc-and PE01364.proved Eq.refl Eq.refl

module r3b_ij247 where

  proved : X47 • X24 ≈ X27 • X47
  proved = by-assoc-and PE01365.proved Eq.refl Eq.refl

module r3b_ij256 where

  proved : X56 • X25 ≈ X26 • X56
  proved = by-assoc-and PE00128.proved Eq.refl Eq.refl

module r3b_ij257 where

  proved : X57 • X25 ≈ X27 • X57
  proved = by-assoc-and PE01366.proved Eq.refl Eq.refl

module r3b_ij267 where

  proved : X67 • X26 ≈ X27 • X67
  proved = by-assoc-and PE00136.proved Eq.refl Eq.refl

module r3b_ij345 where

  proved : X45 • X34 ≈ X35 • X45
  proved = by-assoc-and PE00147.proved Eq.refl Eq.refl

module r3b_ij346 where

  proved : X46 • X34 ≈ X36 • X46
  proved = by-assoc-and PE01367.proved Eq.refl Eq.refl

module r3b_ij347 where

  proved : X47 • X34 ≈ X37 • X47
  proved = by-assoc-and PE01368.proved Eq.refl Eq.refl

module r3b_ij356 where

  proved : X56 • X35 ≈ X36 • X56
  proved = by-assoc-and PE00155.proved Eq.refl Eq.refl

module r3b_ij357 where

  proved : X57 • X35 ≈ X37 • X57
  proved = by-assoc-and PE01369.proved Eq.refl Eq.refl

module r3b_ij367 where

  proved : X67 • X36 ≈ X37 • X67
  proved = by-assoc-and PE00163.proved Eq.refl Eq.refl

module r3b_ij456 where

  proved : X56 • X45 ≈ X46 • X56
  proved = by-assoc-and PE00175.proved Eq.refl Eq.refl

module r3b_ij457 where

  proved : X57 • X45 ≈ X47 • X57
  proved = by-assoc-and PE01370.proved Eq.refl Eq.refl

module r3b_ij467 where

  proved : X67 • X46 ≈ X47 • X67
  proved = by-assoc-and PE00183.proved Eq.refl Eq.refl

module r3b_ij567 where

  proved : X67 • X56 ≈ X57 • X67
  proved = by-assoc-and PE00196.proved Eq.refl Eq.refl
