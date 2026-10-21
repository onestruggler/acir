{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_B02 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00011 ; module PE00012 ; module PE00013 ; module PE00019 ; module PE00020 ; module PE00021 ; module PE00028 ; module PE00029 ; module PE00037 ; module PE00043 ; module PE00051 ; module PE00052)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B002 using (module PE00059 ; module PE00060 ; module PE00061 ; module PE00071 ; module PE00072 ; module PE00073 ; module PE00079 ; module PE00080 ; module PE00087 ; module PE00092 ; module PE00099 ; module PE00100 ; module PE00106 ; module PE00107 ; module PE00108)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B003 using (module PE00113 ; module PE00114 ; module PE00121 ; module PE00126 ; module PE00133 ; module PE00134 ; module PE00140 ; module PE00141 ; module PE00142 ; module PE00148 ; module PE00161 ; module PE00168 ; module PE00169)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B004 using (module PE00189 ; module PE00194 ; module PE00200 ; module PE00207 ; module PE00208)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B023 using (module PE01199 ; module PE01200 ; module PE01201 ; module PE01202 ; module PE01203 ; module PE01204 ; module PE01205 ; module PE01206 ; module PE01207 ; module PE01208 ; module PE01209 ; module PE01210 ; module PE01211 ; module PE01212 ; module PE01213 ; module PE01214 ; module PE01215 ; module PE01216 ; module PE01217 ; module PE01218 ; module PE01219 ; module PE01220 ; module PE01221 ; module PE01222 ; module PE01223 ; module PE01224 ; module PE01225 ; module PE01226 ; module PE01227 ; module PE01228 ; module PE01229 ; module PE01230 ; module PE01231 ; module PE01232 ; module PE01233 ; module PE01234 ; module PE01235 ; module PE01236 ; module PE01237 ; module PE01238 ; module PE01239 ; module PE01240 ; module PE01241 ; module PE01242 ; module PE01243 ; module PE01244 ; module PE01245 ; module PE01246 ; module PE01247 ; module PE01248 ; module PE01249 ; module PE01250 ; module PE01251 ; module PE01252)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B024 using (module PE01253 ; module PE01254 ; module PE01255 ; module PE01256 ; module PE01257 ; module PE01258 ; module PE01259 ; module PE01260 ; module PE01261 ; module PE01262 ; module PE01263 ; module PE01264 ; module PE01265 ; module PE01266 ; module PE01267 ; module PE01268 ; module PE01269 ; module PE01270 ; module PE01271 ; module PE01272 ; module PE01273 ; module PE01274 ; module PE01275 ; module PE01276 ; module PE01277 ; module PE01278 ; module PE01279 ; module PE01280 ; module PE01281 ; module PE01282 ; module PE01283)

module r2a_ij2713 where

  proved : X27 • X13 ≈ X13 • X27
  proved = by-assoc-and PE01199.proved Eq.refl Eq.refl

module r2a_ij2714 where

  proved : X27 • X14 ≈ X14 • X27
  proved = by-assoc-and PE01200.proved Eq.refl Eq.refl

module r2a_ij2715 where

  proved : X27 • X15 ≈ X15 • X27
  proved = by-assoc-and PE01201.proved Eq.refl Eq.refl

module r2a_ij2716 where

  proved : X27 • X16 ≈ X16 • X27
  proved = by-assoc-and PE01202.proved Eq.refl Eq.refl

module r2a_ij2734 where

  proved : X27 • X34 ≈ X34 • X27
  proved = by-assoc-and PE01203.proved Eq.refl Eq.refl

module r2a_ij2735 where

  proved : X27 • X35 ≈ X35 • X27
  proved = by-assoc-and PE01204.proved Eq.refl Eq.refl

module r2a_ij2736 where

  proved : X27 • X36 ≈ X36 • X27
  proved = by-assoc-and PE01205.proved Eq.refl Eq.refl

module r2a_ij2745 where

  proved : X27 • X45 ≈ X45 • X27
  proved = by-assoc-and PE01206.proved Eq.refl Eq.refl

module r2a_ij2746 where

  proved : X27 • X46 ≈ X46 • X27
  proved = by-assoc-and PE01207.proved Eq.refl Eq.refl

module r2a_ij2756 where

  proved : X27 • X56 ≈ X56 • X27
  proved = by-assoc-and PE01208.proved Eq.refl Eq.refl

module r2a_ij3401 where

  proved : X34 • X01 ≈ X01 • X34
  proved = by-assoc-and PE00011.proved Eq.refl Eq.refl

module r2a_ij3402 where

  proved : X34 • X02 ≈ X02 • X34
  proved = by-assoc-and PE00019.proved Eq.refl Eq.refl

module r2a_ij3405 where

  proved : X34 • X05 ≈ X05 • X34
  proved = by-assoc-and PE00043.proved Eq.refl Eq.refl

module r2a_ij3406 where

  proved : X34 • X06 ≈ X06 • X34
  proved = by-assoc-and PE00051.proved Eq.refl Eq.refl

module r2a_ij3407 where

  proved : X34 • X07 ≈ X07 • X34
  proved = by-assoc-and PE00059.proved Eq.refl Eq.refl

module r2a_ij3412 where

  proved : X34 • X12 ≈ X12 • X34
  proved = by-assoc-and PE00071.proved Eq.refl Eq.refl

module r2a_ij3415 where

  proved : X34 • X15 ≈ X15 • X34
  proved = by-assoc-and PE00092.proved Eq.refl Eq.refl

module r2a_ij3416 where

  proved : X34 • X16 ≈ X16 • X34
  proved = by-assoc-and PE00099.proved Eq.refl Eq.refl

module r2a_ij3417 where

  proved : X34 • X17 ≈ X17 • X34
  proved = by-assoc-and PE00106.proved Eq.refl Eq.refl

module r2a_ij3425 where

  proved : X34 • X25 ≈ X25 • X34
  proved = by-assoc-and PE00126.proved Eq.refl Eq.refl

module r2a_ij3426 where

  proved : X34 • X26 ≈ X26 • X34
  proved = by-assoc-and PE00133.proved Eq.refl Eq.refl

module r2a_ij3427 where

  proved : X34 • X27 ≈ X27 • X34
  proved = by-assoc-and PE00140.proved Eq.refl Eq.refl

module r2a_ij3456 where

  proved : X34 • X56 ≈ X56 • X34
  proved = by-assoc-and PE00194.proved Eq.refl Eq.refl

module r2a_ij3457 where

  proved : X34 • X57 ≈ X57 • X34
  proved = by-assoc-and PE00200.proved Eq.refl Eq.refl

module r2a_ij3467 where

  proved : X34 • X67 ≈ X67 • X34
  proved = by-assoc-and PE00207.proved Eq.refl Eq.refl

module r2a_ij3501 where

  proved : X35 • X01 ≈ X01 • X35
  proved = by-assoc-and PE01209.proved Eq.refl Eq.refl

module r2a_ij3502 where

  proved : X35 • X02 ≈ X02 • X35
  proved = by-assoc-and PE01210.proved Eq.refl Eq.refl

module r2a_ij3504 where

  proved : X35 • X04 ≈ X04 • X35
  proved = by-assoc-and PE01211.proved Eq.refl Eq.refl

module r2a_ij3506 where

  proved : X35 • X06 ≈ X06 • X35
  proved = by-assoc-and PE01212.proved Eq.refl Eq.refl

module r2a_ij3507 where

  proved : X35 • X07 ≈ X07 • X35
  proved = by-assoc-and PE01213.proved Eq.refl Eq.refl

module r2a_ij3512 where

  proved : X35 • X12 ≈ X12 • X35
  proved = by-assoc-and PE01214.proved Eq.refl Eq.refl

module r2a_ij3514 where

  proved : X35 • X14 ≈ X14 • X35
  proved = by-assoc-and PE01215.proved Eq.refl Eq.refl

module r2a_ij3516 where

  proved : X35 • X16 ≈ X16 • X35
  proved = by-assoc-and PE01216.proved Eq.refl Eq.refl

module r2a_ij3517 where

  proved : X35 • X17 ≈ X17 • X35
  proved = by-assoc-and PE01217.proved Eq.refl Eq.refl

module r2a_ij3524 where

  proved : X35 • X24 ≈ X24 • X35
  proved = by-assoc-and PE01218.proved Eq.refl Eq.refl

module r2a_ij3526 where

  proved : X35 • X26 ≈ X26 • X35
  proved = by-assoc-and PE01219.proved Eq.refl Eq.refl

module r2a_ij3527 where

  proved : X35 • X27 ≈ X27 • X35
  proved = by-assoc-and PE01220.proved Eq.refl Eq.refl

module r2a_ij3546 where

  proved : X35 • X46 ≈ X46 • X35
  proved = by-assoc-and PE01221.proved Eq.refl Eq.refl

module r2a_ij3547 where

  proved : X35 • X47 ≈ X47 • X35
  proved = by-assoc-and PE01222.proved Eq.refl Eq.refl

module r2a_ij3567 where

  proved : X35 • X67 ≈ X67 • X35
  proved = by-assoc-and PE01223.proved Eq.refl Eq.refl

module r2a_ij3601 where

  proved : X36 • X01 ≈ X01 • X36
  proved = by-assoc-and PE01224.proved Eq.refl Eq.refl

module r2a_ij3602 where

  proved : X36 • X02 ≈ X02 • X36
  proved = by-assoc-and PE01225.proved Eq.refl Eq.refl

module r2a_ij3604 where

  proved : X36 • X04 ≈ X04 • X36
  proved = by-assoc-and PE01226.proved Eq.refl Eq.refl

module r2a_ij3605 where

  proved : X36 • X05 ≈ X05 • X36
  proved = by-assoc-and PE01227.proved Eq.refl Eq.refl

module r2a_ij3607 where

  proved : X36 • X07 ≈ X07 • X36
  proved = by-assoc-and PE01228.proved Eq.refl Eq.refl

module r2a_ij3612 where

  proved : X36 • X12 ≈ X12 • X36
  proved = by-assoc-and PE01229.proved Eq.refl Eq.refl

module r2a_ij3614 where

  proved : X36 • X14 ≈ X14 • X36
  proved = by-assoc-and PE01230.proved Eq.refl Eq.refl

module r2a_ij3615 where

  proved : X36 • X15 ≈ X15 • X36
  proved = by-assoc-and PE01231.proved Eq.refl Eq.refl

module r2a_ij3617 where

  proved : X36 • X17 ≈ X17 • X36
  proved = by-assoc-and PE01232.proved Eq.refl Eq.refl

module r2a_ij3624 where

  proved : X36 • X24 ≈ X24 • X36
  proved = by-assoc-and PE01233.proved Eq.refl Eq.refl

module r2a_ij3625 where

  proved : X36 • X25 ≈ X25 • X36
  proved = by-assoc-and PE01234.proved Eq.refl Eq.refl

module r2a_ij3627 where

  proved : X36 • X27 ≈ X27 • X36
  proved = by-assoc-and PE01235.proved Eq.refl Eq.refl

module r2a_ij3645 where

  proved : X36 • X45 ≈ X45 • X36
  proved = by-assoc-and PE01236.proved Eq.refl Eq.refl

module r2a_ij3647 where

  proved : X36 • X47 ≈ X47 • X36
  proved = by-assoc-and PE01237.proved Eq.refl Eq.refl

module r2a_ij3657 where

  proved : X36 • X57 ≈ X57 • X36
  proved = by-assoc-and PE01238.proved Eq.refl Eq.refl

module r2a_ij3701 where

  proved : X37 • X01 ≈ X01 • X37
  proved = by-assoc-and PE01239.proved Eq.refl Eq.refl

module r2a_ij3702 where

  proved : X37 • X02 ≈ X02 • X37
  proved = by-assoc-and PE01240.proved Eq.refl Eq.refl

module r2a_ij3704 where

  proved : X37 • X04 ≈ X04 • X37
  proved = by-assoc-and PE01241.proved Eq.refl Eq.refl

module r2a_ij3705 where

  proved : X37 • X05 ≈ X05 • X37
  proved = by-assoc-and PE01242.proved Eq.refl Eq.refl

module r2a_ij3706 where

  proved : X37 • X06 ≈ X06 • X37
  proved = by-assoc-and PE01243.proved Eq.refl Eq.refl

module r2a_ij3712 where

  proved : X37 • X12 ≈ X12 • X37
  proved = by-assoc-and PE01244.proved Eq.refl Eq.refl

module r2a_ij3714 where

  proved : X37 • X14 ≈ X14 • X37
  proved = by-assoc-and PE01245.proved Eq.refl Eq.refl

module r2a_ij3715 where

  proved : X37 • X15 ≈ X15 • X37
  proved = by-assoc-and PE01246.proved Eq.refl Eq.refl

module r2a_ij3716 where

  proved : X37 • X16 ≈ X16 • X37
  proved = by-assoc-and PE01247.proved Eq.refl Eq.refl

module r2a_ij3724 where

  proved : X37 • X24 ≈ X24 • X37
  proved = by-assoc-and PE01248.proved Eq.refl Eq.refl

module r2a_ij3725 where

  proved : X37 • X25 ≈ X25 • X37
  proved = by-assoc-and PE01249.proved Eq.refl Eq.refl

module r2a_ij3726 where

  proved : X37 • X26 ≈ X26 • X37
  proved = by-assoc-and PE01250.proved Eq.refl Eq.refl

module r2a_ij3745 where

  proved : X37 • X45 ≈ X45 • X37
  proved = by-assoc-and PE01251.proved Eq.refl Eq.refl

module r2a_ij3746 where

  proved : X37 • X46 ≈ X46 • X37
  proved = by-assoc-and PE01252.proved Eq.refl Eq.refl

module r2a_ij3756 where

  proved : X37 • X56 ≈ X56 • X37
  proved = by-assoc-and PE01253.proved Eq.refl Eq.refl

module r2a_ij4501 where

  proved : X45 • X01 ≈ X01 • X45
  proved = by-assoc-and PE00012.proved Eq.refl Eq.refl

module r2a_ij4502 where

  proved : X45 • X02 ≈ X02 • X45
  proved = by-assoc-and PE00020.proved Eq.refl Eq.refl

module r2a_ij4503 where

  proved : X45 • X03 ≈ X03 • X45
  proved = by-assoc-and PE00028.proved Eq.refl Eq.refl

module r2a_ij4506 where

  proved : X45 • X06 ≈ X06 • X45
  proved = by-assoc-and PE00052.proved Eq.refl Eq.refl

module r2a_ij4507 where

  proved : X45 • X07 ≈ X07 • X45
  proved = by-assoc-and PE00060.proved Eq.refl Eq.refl

module r2a_ij4512 where

  proved : X45 • X12 ≈ X12 • X45
  proved = by-assoc-and PE00072.proved Eq.refl Eq.refl

module r2a_ij4513 where

  proved : X45 • X13 ≈ X13 • X45
  proved = by-assoc-and PE00079.proved Eq.refl Eq.refl

module r2a_ij4516 where

  proved : X45 • X16 ≈ X16 • X45
  proved = by-assoc-and PE00100.proved Eq.refl Eq.refl

module r2a_ij4517 where

  proved : X45 • X17 ≈ X17 • X45
  proved = by-assoc-and PE00107.proved Eq.refl Eq.refl

module r2a_ij4523 where

  proved : X45 • X23 ≈ X23 • X45
  proved = by-assoc-and PE00113.proved Eq.refl Eq.refl

module r2a_ij4526 where

  proved : X45 • X26 ≈ X26 • X45
  proved = by-assoc-and PE00134.proved Eq.refl Eq.refl

module r2a_ij4527 where

  proved : X45 • X27 ≈ X27 • X45
  proved = by-assoc-and PE00141.proved Eq.refl Eq.refl

module r2a_ij4536 where

  proved : X45 • X36 ≈ X36 • X45
  proved = by-assoc-and PE00161.proved Eq.refl Eq.refl

module r2a_ij4537 where

  proved : X45 • X37 ≈ X37 • X45
  proved = by-assoc-and PE00168.proved Eq.refl Eq.refl

module r2a_ij4567 where

  proved : X45 • X67 ≈ X67 • X45
  proved = by-assoc-and PE00208.proved Eq.refl Eq.refl

module r2a_ij4601 where

  proved : X46 • X01 ≈ X01 • X46
  proved = by-assoc-and PE01254.proved Eq.refl Eq.refl

module r2a_ij4602 where

  proved : X46 • X02 ≈ X02 • X46
  proved = by-assoc-and PE01255.proved Eq.refl Eq.refl

module r2a_ij4603 where

  proved : X46 • X03 ≈ X03 • X46
  proved = by-assoc-and PE01256.proved Eq.refl Eq.refl

module r2a_ij4605 where

  proved : X46 • X05 ≈ X05 • X46
  proved = by-assoc-and PE01257.proved Eq.refl Eq.refl

module r2a_ij4607 where

  proved : X46 • X07 ≈ X07 • X46
  proved = by-assoc-and PE01258.proved Eq.refl Eq.refl

module r2a_ij4612 where

  proved : X46 • X12 ≈ X12 • X46
  proved = by-assoc-and PE01259.proved Eq.refl Eq.refl

module r2a_ij4613 where

  proved : X46 • X13 ≈ X13 • X46
  proved = by-assoc-and PE01260.proved Eq.refl Eq.refl

module r2a_ij4615 where

  proved : X46 • X15 ≈ X15 • X46
  proved = by-assoc-and PE01261.proved Eq.refl Eq.refl

module r2a_ij4617 where

  proved : X46 • X17 ≈ X17 • X46
  proved = by-assoc-and PE01262.proved Eq.refl Eq.refl

module r2a_ij4623 where

  proved : X46 • X23 ≈ X23 • X46
  proved = by-assoc-and PE01263.proved Eq.refl Eq.refl

module r2a_ij4625 where

  proved : X46 • X25 ≈ X25 • X46
  proved = by-assoc-and PE01264.proved Eq.refl Eq.refl

module r2a_ij4627 where

  proved : X46 • X27 ≈ X27 • X46
  proved = by-assoc-and PE01265.proved Eq.refl Eq.refl

module r2a_ij4635 where

  proved : X46 • X35 ≈ X35 • X46
  proved = by-assoc-and PE01266.proved Eq.refl Eq.refl

module r2a_ij4637 where

  proved : X46 • X37 ≈ X37 • X46
  proved = by-assoc-and PE01267.proved Eq.refl Eq.refl

module r2a_ij4657 where

  proved : X46 • X57 ≈ X57 • X46
  proved = by-assoc-and PE01268.proved Eq.refl Eq.refl

module r2a_ij4701 where

  proved : X47 • X01 ≈ X01 • X47
  proved = by-assoc-and PE01269.proved Eq.refl Eq.refl

module r2a_ij4702 where

  proved : X47 • X02 ≈ X02 • X47
  proved = by-assoc-and PE01270.proved Eq.refl Eq.refl

module r2a_ij4703 where

  proved : X47 • X03 ≈ X03 • X47
  proved = by-assoc-and PE01271.proved Eq.refl Eq.refl

module r2a_ij4705 where

  proved : X47 • X05 ≈ X05 • X47
  proved = by-assoc-and PE01272.proved Eq.refl Eq.refl

module r2a_ij4706 where

  proved : X47 • X06 ≈ X06 • X47
  proved = by-assoc-and PE01273.proved Eq.refl Eq.refl

module r2a_ij4712 where

  proved : X47 • X12 ≈ X12 • X47
  proved = by-assoc-and PE01274.proved Eq.refl Eq.refl

module r2a_ij4713 where

  proved : X47 • X13 ≈ X13 • X47
  proved = by-assoc-and PE01275.proved Eq.refl Eq.refl

module r2a_ij4715 where

  proved : X47 • X15 ≈ X15 • X47
  proved = by-assoc-and PE01276.proved Eq.refl Eq.refl

module r2a_ij4716 where

  proved : X47 • X16 ≈ X16 • X47
  proved = by-assoc-and PE01277.proved Eq.refl Eq.refl

module r2a_ij4723 where

  proved : X47 • X23 ≈ X23 • X47
  proved = by-assoc-and PE01278.proved Eq.refl Eq.refl

module r2a_ij4725 where

  proved : X47 • X25 ≈ X25 • X47
  proved = by-assoc-and PE01279.proved Eq.refl Eq.refl

module r2a_ij4726 where

  proved : X47 • X26 ≈ X26 • X47
  proved = by-assoc-and PE01280.proved Eq.refl Eq.refl

module r2a_ij4735 where

  proved : X47 • X35 ≈ X35 • X47
  proved = by-assoc-and PE01281.proved Eq.refl Eq.refl

module r2a_ij4736 where

  proved : X47 • X36 ≈ X36 • X47
  proved = by-assoc-and PE01282.proved Eq.refl Eq.refl

module r2a_ij4756 where

  proved : X47 • X56 ≈ X56 • X47
  proved = by-assoc-and PE01283.proved Eq.refl Eq.refl

module r2a_ij5601 where

  proved : X56 • X01 ≈ X01 • X56
  proved = by-assoc-and PE00013.proved Eq.refl Eq.refl

module r2a_ij5602 where

  proved : X56 • X02 ≈ X02 • X56
  proved = by-assoc-and PE00021.proved Eq.refl Eq.refl

module r2a_ij5603 where

  proved : X56 • X03 ≈ X03 • X56
  proved = by-assoc-and PE00029.proved Eq.refl Eq.refl

module r2a_ij5604 where

  proved : X56 • X04 ≈ X04 • X56
  proved = by-assoc-and PE00037.proved Eq.refl Eq.refl

module r2a_ij5607 where

  proved : X56 • X07 ≈ X07 • X56
  proved = by-assoc-and PE00061.proved Eq.refl Eq.refl

module r2a_ij5612 where

  proved : X56 • X12 ≈ X12 • X56
  proved = by-assoc-and PE00073.proved Eq.refl Eq.refl

module r2a_ij5613 where

  proved : X56 • X13 ≈ X13 • X56
  proved = by-assoc-and PE00080.proved Eq.refl Eq.refl

module r2a_ij5614 where

  proved : X56 • X14 ≈ X14 • X56
  proved = by-assoc-and PE00087.proved Eq.refl Eq.refl

module r2a_ij5617 where

  proved : X56 • X17 ≈ X17 • X56
  proved = by-assoc-and PE00108.proved Eq.refl Eq.refl

module r2a_ij5623 where

  proved : X56 • X23 ≈ X23 • X56
  proved = by-assoc-and PE00114.proved Eq.refl Eq.refl

module r2a_ij5624 where

  proved : X56 • X24 ≈ X24 • X56
  proved = by-assoc-and PE00121.proved Eq.refl Eq.refl

module r2a_ij5627 where

  proved : X56 • X27 ≈ X27 • X56
  proved = by-assoc-and PE00142.proved Eq.refl Eq.refl

module r2a_ij5634 where

  proved : X56 • X34 ≈ X34 • X56
  proved = by-assoc-and PE00148.proved Eq.refl Eq.refl

module r2a_ij5637 where

  proved : X56 • X37 ≈ X37 • X56
  proved = by-assoc-and PE00169.proved Eq.refl Eq.refl

module r2a_ij5647 where

  proved : X56 • X47 ≈ X47 • X56
  proved = by-assoc-and PE00189.proved Eq.refl Eq.refl
