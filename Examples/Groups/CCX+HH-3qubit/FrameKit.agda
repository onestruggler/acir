------------------------------------------------------------------------
-- Kit with the frames: the vocabulary of the frame and transport
-- certificates (see Kit), and •-cancelʳ for the one group-like
-- instance, applied here once rather than in each of the 1310 transport
-- cases that use it.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameKit where

open import Examples.Groups.CCX+HH-3qubit.Kit public
open import Examples.Groups.CCX+HH-3qubit.Frames public
  using (checked ; commute-product ; forget-frame ; move-compose ; move-product
        ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open import Examples.Groups.CCX+HH-3qubit.FrameWords public
  using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137
        ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236
        ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346
        ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234
        ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267
        ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467
        ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457
        ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567
        ; M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7
        ; X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; X16
        ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46
        ; X47 ; X56 ; X57 ; X67)

module GL where
  import Presentation.GroupLike as GLib
  import Examples.Groups.CCX+HH-3qubit.Syntactics as S
  open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
  open GLib.Group-Lemmas S._===_ grouplike public using (•-cancelʳ)
