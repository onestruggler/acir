{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00010 ; module PE00034 ; module PE00042 ; module PE00050)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B002 using (module PE00058 ; module PE00084 ; module PE00091 ; module PE00098 ; module PE00105)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B003 using (module PE00173)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B004 using (module PE00179 ; module PE00186 ; module PE00193 ; module PE00199 ; module PE00206)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B020 using (module PE01084 ; module PE01085 ; module PE01086 ; module PE01087 ; module PE01088 ; module PE01089 ; module PE01090 ; module PE01091 ; module PE01092 ; module PE01093)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B021 using (module PE01094 ; module PE01095 ; module PE01096 ; module PE01097 ; module PE01098 ; module PE01099 ; module PE01100 ; module PE01101 ; module PE01102 ; module PE01103 ; module PE01104 ; module PE01105 ; module PE01106 ; module PE01107 ; module PE01108 ; module PE01109 ; module PE01110 ; module PE01111 ; module PE01112 ; module PE01113 ; module PE01114 ; module PE01115 ; module PE01116 ; module PE01117 ; module PE01118 ; module PE01119 ; module PE01120 ; module PE01121 ; module PE01122 ; module PE01123 ; module PE01124 ; module PE01125 ; module PE01126 ; module PE01127 ; module PE01128 ; module PE01129 ; module PE01130 ; module PE01131 ; module PE01132 ; module PE01133 ; module PE01134 ; module PE01135 ; module PE01136 ; module PE01137 ; module PE01138 ; module PE01139 ; module PE01140 ; module PE01141 ; module PE01142 ; module PE01143 ; module PE01144)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B022 using (module PE01145 ; module PE01146 ; module PE01147 ; module PE01148 ; module PE01149 ; module PE01150 ; module PE01151 ; module PE01152 ; module PE01153 ; module PE01154 ; module PE01155 ; module PE01156 ; module PE01157 ; module PE01158 ; module PE01159 ; module PE01160 ; module PE01161 ; module PE01162 ; module PE01163 ; module PE01164 ; module PE01165 ; module PE01166 ; module PE01167 ; module PE01168 ; module PE01169 ; module PE01170 ; module PE01171 ; module PE01172 ; module PE01173 ; module PE01174 ; module PE01175 ; module PE01176 ; module PE01177 ; module PE01178 ; module PE01179 ; module PE01180 ; module PE01181 ; module PE01182 ; module PE01183 ; module PE01184 ; module PE01185 ; module PE01186 ; module PE01187 ; module PE01188 ; module PE01189 ; module PE01190 ; module PE01191 ; module PE01192 ; module PE01193 ; module PE01194 ; module PE01195 ; module PE01196 ; module PE01197 ; module PE01198)

module r2a_ij1346 where

  proved : X13 • X46 ≈ X46 • X13
  proved = by-assoc-and PE01084.proved Eq.refl Eq.refl

module r2a_ij1347 where

  proved : X13 • X47 ≈ X47 • X13
  proved = by-assoc-and PE01085.proved Eq.refl Eq.refl

module r2a_ij1356 where

  proved : X13 • X56 ≈ X56 • X13
  proved = by-assoc-and PE01086.proved Eq.refl Eq.refl

module r2a_ij1357 where

  proved : X13 • X57 ≈ X57 • X13
  proved = by-assoc-and PE01087.proved Eq.refl Eq.refl

module r2a_ij1367 where

  proved : X13 • X67 ≈ X67 • X13
  proved = by-assoc-and PE01088.proved Eq.refl Eq.refl

module r2a_ij1402 where

  proved : X14 • X02 ≈ X02 • X14
  proved = by-assoc-and PE01089.proved Eq.refl Eq.refl

module r2a_ij1403 where

  proved : X14 • X03 ≈ X03 • X14
  proved = by-assoc-and PE01090.proved Eq.refl Eq.refl

module r2a_ij1405 where

  proved : X14 • X05 ≈ X05 • X14
  proved = by-assoc-and PE01091.proved Eq.refl Eq.refl

module r2a_ij1406 where

  proved : X14 • X06 ≈ X06 • X14
  proved = by-assoc-and PE01092.proved Eq.refl Eq.refl

module r2a_ij1407 where

  proved : X14 • X07 ≈ X07 • X14
  proved = by-assoc-and PE01093.proved Eq.refl Eq.refl

module r2a_ij1423 where

  proved : X14 • X23 ≈ X23 • X14
  proved = by-assoc-and PE01094.proved Eq.refl Eq.refl

module r2a_ij1425 where

  proved : X14 • X25 ≈ X25 • X14
  proved = by-assoc-and PE01095.proved Eq.refl Eq.refl

module r2a_ij1426 where

  proved : X14 • X26 ≈ X26 • X14
  proved = by-assoc-and PE01096.proved Eq.refl Eq.refl

module r2a_ij1427 where

  proved : X14 • X27 ≈ X27 • X14
  proved = by-assoc-and PE01097.proved Eq.refl Eq.refl

module r2a_ij1435 where

  proved : X14 • X35 ≈ X35 • X14
  proved = by-assoc-and PE01098.proved Eq.refl Eq.refl

module r2a_ij1436 where

  proved : X14 • X36 ≈ X36 • X14
  proved = by-assoc-and PE01099.proved Eq.refl Eq.refl

module r2a_ij1437 where

  proved : X14 • X37 ≈ X37 • X14
  proved = by-assoc-and PE01100.proved Eq.refl Eq.refl

module r2a_ij1456 where

  proved : X14 • X56 ≈ X56 • X14
  proved = by-assoc-and PE01101.proved Eq.refl Eq.refl

module r2a_ij1457 where

  proved : X14 • X57 ≈ X57 • X14
  proved = by-assoc-and PE01102.proved Eq.refl Eq.refl

module r2a_ij1467 where

  proved : X14 • X67 ≈ X67 • X14
  proved = by-assoc-and PE01103.proved Eq.refl Eq.refl

module r2a_ij1502 where

  proved : X15 • X02 ≈ X02 • X15
  proved = by-assoc-and PE01104.proved Eq.refl Eq.refl

module r2a_ij1503 where

  proved : X15 • X03 ≈ X03 • X15
  proved = by-assoc-and PE01105.proved Eq.refl Eq.refl

module r2a_ij1504 where

  proved : X15 • X04 ≈ X04 • X15
  proved = by-assoc-and PE01106.proved Eq.refl Eq.refl

module r2a_ij1506 where

  proved : X15 • X06 ≈ X06 • X15
  proved = by-assoc-and PE01107.proved Eq.refl Eq.refl

module r2a_ij1507 where

  proved : X15 • X07 ≈ X07 • X15
  proved = by-assoc-and PE01108.proved Eq.refl Eq.refl

module r2a_ij1523 where

  proved : X15 • X23 ≈ X23 • X15
  proved = by-assoc-and PE01109.proved Eq.refl Eq.refl

module r2a_ij1524 where

  proved : X15 • X24 ≈ X24 • X15
  proved = by-assoc-and PE01110.proved Eq.refl Eq.refl

module r2a_ij1526 where

  proved : X15 • X26 ≈ X26 • X15
  proved = by-assoc-and PE01111.proved Eq.refl Eq.refl

module r2a_ij1527 where

  proved : X15 • X27 ≈ X27 • X15
  proved = by-assoc-and PE01112.proved Eq.refl Eq.refl

module r2a_ij1534 where

  proved : X15 • X34 ≈ X34 • X15
  proved = by-assoc-and PE01113.proved Eq.refl Eq.refl

module r2a_ij1536 where

  proved : X15 • X36 ≈ X36 • X15
  proved = by-assoc-and PE01114.proved Eq.refl Eq.refl

module r2a_ij1537 where

  proved : X15 • X37 ≈ X37 • X15
  proved = by-assoc-and PE01115.proved Eq.refl Eq.refl

module r2a_ij1546 where

  proved : X15 • X46 ≈ X46 • X15
  proved = by-assoc-and PE01116.proved Eq.refl Eq.refl

module r2a_ij1547 where

  proved : X15 • X47 ≈ X47 • X15
  proved = by-assoc-and PE01117.proved Eq.refl Eq.refl

module r2a_ij1567 where

  proved : X15 • X67 ≈ X67 • X15
  proved = by-assoc-and PE01118.proved Eq.refl Eq.refl

module r2a_ij1602 where

  proved : X16 • X02 ≈ X02 • X16
  proved = by-assoc-and PE01119.proved Eq.refl Eq.refl

module r2a_ij1603 where

  proved : X16 • X03 ≈ X03 • X16
  proved = by-assoc-and PE01120.proved Eq.refl Eq.refl

module r2a_ij1604 where

  proved : X16 • X04 ≈ X04 • X16
  proved = by-assoc-and PE01121.proved Eq.refl Eq.refl

module r2a_ij1605 where

  proved : X16 • X05 ≈ X05 • X16
  proved = by-assoc-and PE01122.proved Eq.refl Eq.refl

module r2a_ij1607 where

  proved : X16 • X07 ≈ X07 • X16
  proved = by-assoc-and PE01123.proved Eq.refl Eq.refl

module r2a_ij1623 where

  proved : X16 • X23 ≈ X23 • X16
  proved = by-assoc-and PE01124.proved Eq.refl Eq.refl

module r2a_ij1624 where

  proved : X16 • X24 ≈ X24 • X16
  proved = by-assoc-and PE01125.proved Eq.refl Eq.refl

module r2a_ij1625 where

  proved : X16 • X25 ≈ X25 • X16
  proved = by-assoc-and PE01126.proved Eq.refl Eq.refl

module r2a_ij1627 where

  proved : X16 • X27 ≈ X27 • X16
  proved = by-assoc-and PE01127.proved Eq.refl Eq.refl

module r2a_ij1634 where

  proved : X16 • X34 ≈ X34 • X16
  proved = by-assoc-and PE01128.proved Eq.refl Eq.refl

module r2a_ij1635 where

  proved : X16 • X35 ≈ X35 • X16
  proved = by-assoc-and PE01129.proved Eq.refl Eq.refl

module r2a_ij1637 where

  proved : X16 • X37 ≈ X37 • X16
  proved = by-assoc-and PE01130.proved Eq.refl Eq.refl

module r2a_ij1645 where

  proved : X16 • X45 ≈ X45 • X16
  proved = by-assoc-and PE01131.proved Eq.refl Eq.refl

module r2a_ij1647 where

  proved : X16 • X47 ≈ X47 • X16
  proved = by-assoc-and PE01132.proved Eq.refl Eq.refl

module r2a_ij1657 where

  proved : X16 • X57 ≈ X57 • X16
  proved = by-assoc-and PE01133.proved Eq.refl Eq.refl

module r2a_ij1702 where

  proved : X17 • X02 ≈ X02 • X17
  proved = by-assoc-and PE01134.proved Eq.refl Eq.refl

module r2a_ij1703 where

  proved : X17 • X03 ≈ X03 • X17
  proved = by-assoc-and PE01135.proved Eq.refl Eq.refl

module r2a_ij1704 where

  proved : X17 • X04 ≈ X04 • X17
  proved = by-assoc-and PE01136.proved Eq.refl Eq.refl

module r2a_ij1705 where

  proved : X17 • X05 ≈ X05 • X17
  proved = by-assoc-and PE01137.proved Eq.refl Eq.refl

module r2a_ij1706 where

  proved : X17 • X06 ≈ X06 • X17
  proved = by-assoc-and PE01138.proved Eq.refl Eq.refl

module r2a_ij1723 where

  proved : X17 • X23 ≈ X23 • X17
  proved = by-assoc-and PE01139.proved Eq.refl Eq.refl

module r2a_ij1724 where

  proved : X17 • X24 ≈ X24 • X17
  proved = by-assoc-and PE01140.proved Eq.refl Eq.refl

module r2a_ij1725 where

  proved : X17 • X25 ≈ X25 • X17
  proved = by-assoc-and PE01141.proved Eq.refl Eq.refl

module r2a_ij1726 where

  proved : X17 • X26 ≈ X26 • X17
  proved = by-assoc-and PE01142.proved Eq.refl Eq.refl

module r2a_ij1734 where

  proved : X17 • X34 ≈ X34 • X17
  proved = by-assoc-and PE01143.proved Eq.refl Eq.refl

module r2a_ij1735 where

  proved : X17 • X35 ≈ X35 • X17
  proved = by-assoc-and PE01144.proved Eq.refl Eq.refl

module r2a_ij1736 where

  proved : X17 • X36 ≈ X36 • X17
  proved = by-assoc-and PE01145.proved Eq.refl Eq.refl

module r2a_ij1745 where

  proved : X17 • X45 ≈ X45 • X17
  proved = by-assoc-and PE01146.proved Eq.refl Eq.refl

module r2a_ij1746 where

  proved : X17 • X46 ≈ X46 • X17
  proved = by-assoc-and PE01147.proved Eq.refl Eq.refl

module r2a_ij1756 where

  proved : X17 • X56 ≈ X56 • X17
  proved = by-assoc-and PE01148.proved Eq.refl Eq.refl

module r2a_ij2301 where

  proved : X23 • X01 ≈ X01 • X23
  proved = by-assoc-and PE00010.proved Eq.refl Eq.refl

module r2a_ij2304 where

  proved : X23 • X04 ≈ X04 • X23
  proved = by-assoc-and PE00034.proved Eq.refl Eq.refl

module r2a_ij2305 where

  proved : X23 • X05 ≈ X05 • X23
  proved = by-assoc-and PE00042.proved Eq.refl Eq.refl

module r2a_ij2306 where

  proved : X23 • X06 ≈ X06 • X23
  proved = by-assoc-and PE00050.proved Eq.refl Eq.refl

module r2a_ij2307 where

  proved : X23 • X07 ≈ X07 • X23
  proved = by-assoc-and PE00058.proved Eq.refl Eq.refl

module r2a_ij2314 where

  proved : X23 • X14 ≈ X14 • X23
  proved = by-assoc-and PE00084.proved Eq.refl Eq.refl

module r2a_ij2315 where

  proved : X23 • X15 ≈ X15 • X23
  proved = by-assoc-and PE00091.proved Eq.refl Eq.refl

module r2a_ij2316 where

  proved : X23 • X16 ≈ X16 • X23
  proved = by-assoc-and PE00098.proved Eq.refl Eq.refl

module r2a_ij2317 where

  proved : X23 • X17 ≈ X17 • X23
  proved = by-assoc-and PE00105.proved Eq.refl Eq.refl

module r2a_ij2345 where

  proved : X23 • X45 ≈ X45 • X23
  proved = by-assoc-and PE00173.proved Eq.refl Eq.refl

module r2a_ij2346 where

  proved : X23 • X46 ≈ X46 • X23
  proved = by-assoc-and PE00179.proved Eq.refl Eq.refl

module r2a_ij2347 where

  proved : X23 • X47 ≈ X47 • X23
  proved = by-assoc-and PE00186.proved Eq.refl Eq.refl

module r2a_ij2356 where

  proved : X23 • X56 ≈ X56 • X23
  proved = by-assoc-and PE00193.proved Eq.refl Eq.refl

module r2a_ij2357 where

  proved : X23 • X57 ≈ X57 • X23
  proved = by-assoc-and PE00199.proved Eq.refl Eq.refl

module r2a_ij2367 where

  proved : X23 • X67 ≈ X67 • X23
  proved = by-assoc-and PE00206.proved Eq.refl Eq.refl

module r2a_ij2401 where

  proved : X24 • X01 ≈ X01 • X24
  proved = by-assoc-and PE01149.proved Eq.refl Eq.refl

module r2a_ij2403 where

  proved : X24 • X03 ≈ X03 • X24
  proved = by-assoc-and PE01150.proved Eq.refl Eq.refl

module r2a_ij2405 where

  proved : X24 • X05 ≈ X05 • X24
  proved = by-assoc-and PE01151.proved Eq.refl Eq.refl

module r2a_ij2406 where

  proved : X24 • X06 ≈ X06 • X24
  proved = by-assoc-and PE01152.proved Eq.refl Eq.refl

module r2a_ij2407 where

  proved : X24 • X07 ≈ X07 • X24
  proved = by-assoc-and PE01153.proved Eq.refl Eq.refl

module r2a_ij2413 where

  proved : X24 • X13 ≈ X13 • X24
  proved = by-assoc-and PE01154.proved Eq.refl Eq.refl

module r2a_ij2415 where

  proved : X24 • X15 ≈ X15 • X24
  proved = by-assoc-and PE01155.proved Eq.refl Eq.refl

module r2a_ij2416 where

  proved : X24 • X16 ≈ X16 • X24
  proved = by-assoc-and PE01156.proved Eq.refl Eq.refl

module r2a_ij2417 where

  proved : X24 • X17 ≈ X17 • X24
  proved = by-assoc-and PE01157.proved Eq.refl Eq.refl

module r2a_ij2435 where

  proved : X24 • X35 ≈ X35 • X24
  proved = by-assoc-and PE01158.proved Eq.refl Eq.refl

module r2a_ij2436 where

  proved : X24 • X36 ≈ X36 • X24
  proved = by-assoc-and PE01159.proved Eq.refl Eq.refl

module r2a_ij2437 where

  proved : X24 • X37 ≈ X37 • X24
  proved = by-assoc-and PE01160.proved Eq.refl Eq.refl

module r2a_ij2456 where

  proved : X24 • X56 ≈ X56 • X24
  proved = by-assoc-and PE01161.proved Eq.refl Eq.refl

module r2a_ij2457 where

  proved : X24 • X57 ≈ X57 • X24
  proved = by-assoc-and PE01162.proved Eq.refl Eq.refl

module r2a_ij2467 where

  proved : X24 • X67 ≈ X67 • X24
  proved = by-assoc-and PE01163.proved Eq.refl Eq.refl

module r2a_ij2501 where

  proved : X25 • X01 ≈ X01 • X25
  proved = by-assoc-and PE01164.proved Eq.refl Eq.refl

module r2a_ij2503 where

  proved : X25 • X03 ≈ X03 • X25
  proved = by-assoc-and PE01165.proved Eq.refl Eq.refl

module r2a_ij2504 where

  proved : X25 • X04 ≈ X04 • X25
  proved = by-assoc-and PE01166.proved Eq.refl Eq.refl

module r2a_ij2506 where

  proved : X25 • X06 ≈ X06 • X25
  proved = by-assoc-and PE01167.proved Eq.refl Eq.refl

module r2a_ij2507 where

  proved : X25 • X07 ≈ X07 • X25
  proved = by-assoc-and PE01168.proved Eq.refl Eq.refl

module r2a_ij2513 where

  proved : X25 • X13 ≈ X13 • X25
  proved = by-assoc-and PE01169.proved Eq.refl Eq.refl

module r2a_ij2514 where

  proved : X25 • X14 ≈ X14 • X25
  proved = by-assoc-and PE01170.proved Eq.refl Eq.refl

module r2a_ij2516 where

  proved : X25 • X16 ≈ X16 • X25
  proved = by-assoc-and PE01171.proved Eq.refl Eq.refl

module r2a_ij2517 where

  proved : X25 • X17 ≈ X17 • X25
  proved = by-assoc-and PE01172.proved Eq.refl Eq.refl

module r2a_ij2534 where

  proved : X25 • X34 ≈ X34 • X25
  proved = by-assoc-and PE01173.proved Eq.refl Eq.refl

module r2a_ij2536 where

  proved : X25 • X36 ≈ X36 • X25
  proved = by-assoc-and PE01174.proved Eq.refl Eq.refl

module r2a_ij2537 where

  proved : X25 • X37 ≈ X37 • X25
  proved = by-assoc-and PE01175.proved Eq.refl Eq.refl

module r2a_ij2546 where

  proved : X25 • X46 ≈ X46 • X25
  proved = by-assoc-and PE01176.proved Eq.refl Eq.refl

module r2a_ij2547 where

  proved : X25 • X47 ≈ X47 • X25
  proved = by-assoc-and PE01177.proved Eq.refl Eq.refl

module r2a_ij2567 where

  proved : X25 • X67 ≈ X67 • X25
  proved = by-assoc-and PE01178.proved Eq.refl Eq.refl

module r2a_ij2601 where

  proved : X26 • X01 ≈ X01 • X26
  proved = by-assoc-and PE01179.proved Eq.refl Eq.refl

module r2a_ij2603 where

  proved : X26 • X03 ≈ X03 • X26
  proved = by-assoc-and PE01180.proved Eq.refl Eq.refl

module r2a_ij2604 where

  proved : X26 • X04 ≈ X04 • X26
  proved = by-assoc-and PE01181.proved Eq.refl Eq.refl

module r2a_ij2605 where

  proved : X26 • X05 ≈ X05 • X26
  proved = by-assoc-and PE01182.proved Eq.refl Eq.refl

module r2a_ij2607 where

  proved : X26 • X07 ≈ X07 • X26
  proved = by-assoc-and PE01183.proved Eq.refl Eq.refl

module r2a_ij2613 where

  proved : X26 • X13 ≈ X13 • X26
  proved = by-assoc-and PE01184.proved Eq.refl Eq.refl

module r2a_ij2614 where

  proved : X26 • X14 ≈ X14 • X26
  proved = by-assoc-and PE01185.proved Eq.refl Eq.refl

module r2a_ij2615 where

  proved : X26 • X15 ≈ X15 • X26
  proved = by-assoc-and PE01186.proved Eq.refl Eq.refl

module r2a_ij2617 where

  proved : X26 • X17 ≈ X17 • X26
  proved = by-assoc-and PE01187.proved Eq.refl Eq.refl

module r2a_ij2634 where

  proved : X26 • X34 ≈ X34 • X26
  proved = by-assoc-and PE01188.proved Eq.refl Eq.refl

module r2a_ij2635 where

  proved : X26 • X35 ≈ X35 • X26
  proved = by-assoc-and PE01189.proved Eq.refl Eq.refl

module r2a_ij2637 where

  proved : X26 • X37 ≈ X37 • X26
  proved = by-assoc-and PE01190.proved Eq.refl Eq.refl

module r2a_ij2645 where

  proved : X26 • X45 ≈ X45 • X26
  proved = by-assoc-and PE01191.proved Eq.refl Eq.refl

module r2a_ij2647 where

  proved : X26 • X47 ≈ X47 • X26
  proved = by-assoc-and PE01192.proved Eq.refl Eq.refl

module r2a_ij2657 where

  proved : X26 • X57 ≈ X57 • X26
  proved = by-assoc-and PE01193.proved Eq.refl Eq.refl

module r2a_ij2701 where

  proved : X27 • X01 ≈ X01 • X27
  proved = by-assoc-and PE01194.proved Eq.refl Eq.refl

module r2a_ij2703 where

  proved : X27 • X03 ≈ X03 • X27
  proved = by-assoc-and PE01195.proved Eq.refl Eq.refl

module r2a_ij2704 where

  proved : X27 • X04 ≈ X04 • X27
  proved = by-assoc-and PE01196.proved Eq.refl Eq.refl

module r2a_ij2705 where

  proved : X27 • X05 ≈ X05 • X27
  proved = by-assoc-and PE01197.proved Eq.refl Eq.refl

module r2a_ij2706 where

  proved : X27 • X06 ≈ X06 • X27
  proved = by-assoc-and PE01198.proved Eq.refl Eq.refl
