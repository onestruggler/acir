{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B078 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0346 ; K1235 ; K1236 ; K1246 ; K1345 ; K1346 ; K2345 ; K2346 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; M0 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008 ; module MV00251 ; module MV00254 ; module MV00255 ; module MV00257 ; module MV00551 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00016 ; module MV00024 ; module MV00028 ; module MV00029 ; module MV00030)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00252 ; module MV00253 ; module MV00259 ; module MV00260 ; module MV00261 ; module MV00274 ; module MV00280 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00354 ; module MV00356)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00392)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00500 ; module MV00503 ; module MV00505 ; module MV00507 ; module MV00511)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00517 ; module MV00523 ; module MV00525 ; module MV00530 ; module MV00534 ; module MV00535 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00540 ; module MV00545 ; module MV00546 ; module MV00548 ; module MV00552 ; module MV00553 ; module MV00557 ; module MV00561 ; module MV00563)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00566 ; module MV00571 ; module MV00576 ; module MV00578 ; module MV00582 ; module MV00585 ; module MV00587)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00590 ; module MV00592 ; module MV00596 ; module MV00598 ; module MV00600 ; module MV00602 ; module MV00607 ; module MV00608 ; module MV00611)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00612 ; module MV00616 ; module MV00617 ; module MV00621 ; module MV00622 ; module MV00626 ; module MV00627 ; module MV00628)

module MV03091 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0346 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))))))) Eq.refl Eq.refl

module MV03092 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5) • K1345 ≈ K2456 • p (s0 • s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00585.proved (move-compose MV00534.proved (move-compose MV00535.proved (move-compose MV00517.proved (move-compose MV00505.proved (MV00500.proved)))))) Eq.refl Eq.refl

module MV03093 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5) • K2345 ≈ K3456 • p (s0 • s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00607.proved (move-compose MV00608.proved (move-compose MV00587.proved (move-compose MV00571.proved (move-compose MV00561.proved (MV00557.proved)))))) Eq.refl Eq.refl

module MV03094 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5) • K0124 ≈ K1235 • p (s0 • s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00255.proved (move-compose MV00251.proved (MV00252.proved)))))) Eq.refl Eq.refl

module MV03095 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s6 • s5) • K1345 ≈ K2457 • p (s0 • s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00590.proved (move-compose MV00539.proved (move-compose MV00540.proved (move-compose MV00523.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))))))) Eq.refl Eq.refl

module MV03096 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s6 • s5) • K2345 ≈ K3457 • p (s0 • s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00611.proved (move-compose MV00612.proved (move-compose MV00592.proved (move-compose MV00576.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))))))) Eq.refl Eq.refl

module MV03097 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s6 • s5) • K0124 ≈ K1235 • p (s0 • s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00255.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))))))) Eq.refl Eq.refl

module MV03098 where

  proved : p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K2467 • p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00596.proved (move-compose MV00545.proved (move-compose MV00546.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))))) Eq.refl Eq.refl

module MV03099 where

  proved : p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K3467 • p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00616.proved (move-compose MV00617.proved (move-compose MV00598.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))))) Eq.refl Eq.refl

module MV03100 where

  proved : p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K1236 • p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))))) Eq.refl Eq.refl

module MV03101 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K2567 • p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00602.proved (move-compose MV00551.proved (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))))))))) Eq.refl Eq.refl

module MV03102 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K3567 • p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00621.proved (move-compose MV00622.proved (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))))))))) Eq.refl Eq.refl

module MV03103 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K1236 • p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))))))))) Eq.refl Eq.refl

module MV03104 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K2567 • p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00602.proved (move-compose MV00551.proved (move-compose MV00553.proved (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))))))) Eq.refl Eq.refl

module MV03105 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K4567 • p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00626.proved (move-compose MV00627.proved (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))))))) Eq.refl Eq.refl

module MV03106 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K1246 • p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))))))) Eq.refl Eq.refl

module MV03107 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K3567 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00621.proved (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00553.proved (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))))))))))) Eq.refl Eq.refl

module MV03108 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K4567 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00626.proved (move-compose MV00628.proved (move-compose MV00627.proved (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))))))))))) Eq.refl Eq.refl

module MV03109 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))))))))))) Eq.refl Eq.refl

module MV03110 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K3567 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00622.proved (move-compose MV00621.proved (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00553.proved (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))))))))) Eq.refl Eq.refl

module MV03111 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K4567 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00627.proved (move-compose MV00626.proved (move-compose MV00628.proved (move-compose MV00627.proved (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))))))))) Eq.refl Eq.refl

module MV03112 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K2346 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00503.proved (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))))))))) Eq.refl Eq.refl

module MV03113 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • M0 ≈ M4 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00028.proved (move-compose MV00029.proved (move-compose MV00030.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (MV00000.proved))))))) Eq.refl Eq.refl
