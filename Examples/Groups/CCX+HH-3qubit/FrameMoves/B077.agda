{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B077 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0125 ; K0126 ; K0135 ; K0136 ; K0146 ; K0235 ; K0236 ; K0246 ; K1345 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00251 ; module MV00254 ; module MV00255 ; module MV00257 ; module MV00551 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00252 ; module MV00253 ; module MV00259 ; module MV00260 ; module MV00261 ; module MV00274 ; module MV00280 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00500 ; module MV00505 ; module MV00507 ; module MV00511)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00517 ; module MV00523 ; module MV00525 ; module MV00530 ; module MV00534 ; module MV00535 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00540 ; module MV00545 ; module MV00546 ; module MV00548 ; module MV00552 ; module MV00553 ; module MV00557 ; module MV00561 ; module MV00563)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00566 ; module MV00571 ; module MV00576 ; module MV00578 ; module MV00582 ; module MV00587)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592 ; module MV00598 ; module MV00600 ; module MV00608)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00612 ; module MV00617 ; module MV00622 ; module MV00627 ; module MV00628)

module MV03035 where

  proved : p (s6 • s5) • K1345 ≈ K1347 • p (s6 • s5)
  proved = by-assoc-and (move-compose MV00507.proved (MV00500.proved)) Eq.refl Eq.refl

module MV03036 where

  proved : p (s6 • s5) • K2345 ≈ K2347 • p (s6 • s5)
  proved = by-assoc-and (move-compose MV00563.proved (MV00557.proved)) Eq.refl Eq.refl

module MV03037 where

  proved : p (s6 • s5) • K0124 ≈ K0124 • p (s6 • s5)
  proved = by-assoc-and (move-compose MV00253.proved (MV00252.proved)) Eq.refl Eq.refl

module MV03038 where

  proved : p (s4 • s5) • K1345 ≈ K1356 • p (s4 • s5)
  proved = by-assoc-and (move-compose MV00505.proved (MV00500.proved)) Eq.refl Eq.refl

module MV03039 where

  proved : p (s4 • s5) • K2345 ≈ K2356 • p (s4 • s5)
  proved = by-assoc-and (move-compose MV00561.proved (MV00557.proved)) Eq.refl Eq.refl

module MV03040 where

  proved : p (s4 • s5) • K0124 ≈ K0125 • p (s4 • s5)
  proved = by-assoc-and (move-compose MV00251.proved (MV00252.proved)) Eq.refl Eq.refl

module MV03041 where

  proved : p (s4 • s6 • s5) • K1345 ≈ K1357 • p (s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))) Eq.refl Eq.refl

module MV03042 where

  proved : p (s4 • s6 • s5) • K2345 ≈ K2357 • p (s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))) Eq.refl Eq.refl

module MV03043 where

  proved : p (s4 • s6 • s5) • K0124 ≈ K0125 • p (s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))) Eq.refl Eq.refl

module MV03044 where

  proved : p (s5 • s4 • s6 • s5) • K1345 ≈ K1367 • p (s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))) Eq.refl Eq.refl

module MV03045 where

  proved : p (s5 • s4 • s6 • s5) • K2345 ≈ K2367 • p (s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))) Eq.refl Eq.refl

module MV03046 where

  proved : p (s5 • s4 • s6 • s5) • K0124 ≈ K0126 • p (s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))) Eq.refl Eq.refl

module MV03047 where

  proved : p (s3 • s4 • s5) • K1345 ≈ K1456 • p (s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00517.proved (move-compose MV00505.proved (MV00500.proved))) Eq.refl Eq.refl

module MV03048 where

  proved : p (s3 • s4 • s5) • K2345 ≈ K2456 • p (s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00571.proved (move-compose MV00561.proved (MV00557.proved))) Eq.refl Eq.refl

module MV03049 where

  proved : p (s3 • s4 • s5) • K0124 ≈ K0125 • p (s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00255.proved (move-compose MV00251.proved (MV00252.proved))) Eq.refl Eq.refl

module MV03050 where

  proved : p (s3 • s4 • s6 • s5) • K1345 ≈ K1457 • p (s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00523.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))) Eq.refl Eq.refl

module MV03051 where

  proved : p (s3 • s4 • s6 • s5) • K2345 ≈ K2457 • p (s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00576.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))) Eq.refl Eq.refl

module MV03052 where

  proved : p (s3 • s4 • s6 • s5) • K0124 ≈ K0125 • p (s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00255.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))) Eq.refl Eq.refl

module MV03053 where

  proved : p (s3 • s5 • s4 • s6 • s5) • K1345 ≈ K1467 • p (s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))))) Eq.refl Eq.refl

module MV03054 where

  proved : p (s3 • s5 • s4 • s6 • s5) • K2345 ≈ K2467 • p (s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))))) Eq.refl Eq.refl

module MV03055 where

  proved : p (s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0126 • p (s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))))) Eq.refl Eq.refl

module MV03056 where

  proved : p (s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K1567 • p (s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))) Eq.refl Eq.refl

module MV03057 where

  proved : p (s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K2567 • p (s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))) Eq.refl Eq.refl

module MV03058 where

  proved : p (s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0126 • p (s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))) Eq.refl Eq.refl

module MV03059 where

  proved : p (s2 • s3 • s4 • s5) • K1345 ≈ K1456 • p (s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00535.proved (move-compose MV00517.proved (move-compose MV00505.proved (MV00500.proved)))) Eq.refl Eq.refl

module MV03060 where

  proved : p (s2 • s3 • s4 • s5) • K2345 ≈ K3456 • p (s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00587.proved (move-compose MV00571.proved (move-compose MV00561.proved (MV00557.proved)))) Eq.refl Eq.refl

module MV03061 where

  proved : p (s2 • s3 • s4 • s5) • K0124 ≈ K0135 • p (s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00255.proved (move-compose MV00251.proved (MV00252.proved)))) Eq.refl Eq.refl

module MV03062 where

  proved : p (s2 • s3 • s4 • s6 • s5) • K1345 ≈ K1457 • p (s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00540.proved (move-compose MV00523.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))))) Eq.refl Eq.refl

module MV03063 where

  proved : p (s2 • s3 • s4 • s6 • s5) • K2345 ≈ K3457 • p (s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00592.proved (move-compose MV00576.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))))) Eq.refl Eq.refl

module MV03064 where

  proved : p (s2 • s3 • s4 • s6 • s5) • K0124 ≈ K0135 • p (s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00255.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))))) Eq.refl Eq.refl

module MV03065 where

  proved : p (s2 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K1467 • p (s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00546.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))) Eq.refl Eq.refl

module MV03066 where

  proved : p (s2 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K3467 • p (s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00598.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))) Eq.refl Eq.refl

module MV03067 where

  proved : p (s2 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0136 • p (s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))) Eq.refl Eq.refl

module MV03068 where

  proved : p (s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K1567 • p (s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))))))) Eq.refl Eq.refl

module MV03069 where

  proved : p (s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K3567 • p (s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))))))) Eq.refl Eq.refl

module MV03070 where

  proved : p (s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0136 • p (s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))))))) Eq.refl Eq.refl

module MV03071 where

  proved : p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K1567 • p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00553.proved (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))))) Eq.refl Eq.refl

module MV03072 where

  proved : p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K4567 • p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))))) Eq.refl Eq.refl

module MV03073 where

  proved : p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0146 • p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))))) Eq.refl Eq.refl

module MV03074 where

  proved : p (s1 • s2 • s3 • s4 • s5) • K1345 ≈ K2456 • p (s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00535.proved (move-compose MV00517.proved (move-compose MV00505.proved (MV00500.proved))))) Eq.refl Eq.refl

module MV03075 where

  proved : p (s1 • s2 • s3 • s4 • s5) • K2345 ≈ K3456 • p (s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00608.proved (move-compose MV00587.proved (move-compose MV00571.proved (move-compose MV00561.proved (MV00557.proved))))) Eq.refl Eq.refl

module MV03076 where

  proved : p (s1 • s2 • s3 • s4 • s5) • K0124 ≈ K0235 • p (s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00255.proved (move-compose MV00251.proved (MV00252.proved))))) Eq.refl Eq.refl

module MV03077 where

  proved : p (s1 • s2 • s3 • s4 • s6 • s5) • K1345 ≈ K2457 • p (s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00540.proved (move-compose MV00523.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))) Eq.refl Eq.refl

module MV03078 where

  proved : p (s1 • s2 • s3 • s4 • s6 • s5) • K2345 ≈ K3457 • p (s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00612.proved (move-compose MV00592.proved (move-compose MV00576.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))) Eq.refl Eq.refl

module MV03079 where

  proved : p (s1 • s2 • s3 • s4 • s6 • s5) • K0124 ≈ K0235 • p (s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00255.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))) Eq.refl Eq.refl

module MV03080 where

  proved : p (s1 • s2 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K2467 • p (s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00546.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))))))) Eq.refl Eq.refl

module MV03081 where

  proved : p (s1 • s2 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K3467 • p (s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00617.proved (move-compose MV00598.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))))))) Eq.refl Eq.refl

module MV03082 where

  proved : p (s1 • s2 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0236 • p (s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))))))) Eq.refl Eq.refl

module MV03083 where

  proved : p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K2567 • p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))))) Eq.refl Eq.refl

module MV03084 where

  proved : p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K3567 • p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00622.proved (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))))) Eq.refl Eq.refl

module MV03085 where

  proved : p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0236 • p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved)))))))) Eq.refl Eq.refl

module MV03086 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K2567 • p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00553.proved (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved))))))))) Eq.refl Eq.refl

module MV03087 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K4567 • p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00627.proved (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved))))))))) Eq.refl Eq.refl

module MV03088 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0124 ≈ K0246 • p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00261.proved (move-compose MV00260.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00253.proved (MV00252.proved))))))))) Eq.refl Eq.refl

module MV03089 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K1345 ≈ K3567 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00553.proved (move-compose MV00552.proved (move-compose MV00548.proved (move-compose MV00530.proved (move-compose MV00525.proved (move-compose MV00511.proved (move-compose MV00507.proved (MV00500.proved)))))))))) Eq.refl Eq.refl

module MV03090 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K2345 ≈ K4567 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00628.proved (move-compose MV00627.proved (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00600.proved (move-compose MV00582.proved (move-compose MV00578.proved (move-compose MV00566.proved (move-compose MV00563.proved (MV00557.proved)))))))))) Eq.refl Eq.refl
