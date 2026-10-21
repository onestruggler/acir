{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B029 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K1236 ; K1237 ; K1246 ; K1247 ; K1267 ; K1346 ; K1347 ; K1367 ; K1467 ; K2346 ; K2347 ; K2367 ; K2467 ; K2567 ; K3467 ; K3567 ; X04 ; X05 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00551 ; module MV00604)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00077 ; module MV00078 ; module MV00084 ; module MV00085 ; module MV00117)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00124 ; module MV00126 ; module MV00127 ; module MV00128 ; module MV00159 ; module MV00161 ; module MV00168 ; module MV00169 ; module MV00170 ; module MV00187 ; module MV00191 ; module MV00194 ; module MV00196 ; module MV00197 ; module MV00203 ; module MV00204 ; module MV00205 ; module MV00209 ; module MV00210 ; module MV00215 ; module MV00218 ; module MV00222)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00280 ; module MV00282 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00303)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00342 ; module MV00354 ; module MV00356 ; module MV00361 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00381 ; module MV00392 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00417)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00503 ; module MV00509)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00528)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00598)

module MV01116 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X04 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00128.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01117 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl

module MV01118 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X04 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00078.proved (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00128.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))))) Eq.refl Eq.refl

module MV01119 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K3567 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))))) Eq.refl Eq.refl

module MV01120 where

  proved : p (s0 • s1 • s2 • s3) • X45 ≈ X05 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00159.proved (move-compose MV00187.proved (MV00209.proved)))) Eq.refl Eq.refl

module MV01121 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X05 • p (s0 • s1 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00159.proved (move-compose MV00187.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01122 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K1236 • p (s0 • s1 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01123 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X05 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00159.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01124 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K1237 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00342.proved (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01125 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X05 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00159.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01126 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01127 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X05 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00159.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01128 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K1247 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00361.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01129 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X05 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01130 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1267 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00381.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01131 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X05 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01132 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01133 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X05 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01134 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K1347 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01135 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X05 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01136 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1367 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01137 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X05 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01138 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1467 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01139 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X05 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01140 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K2346 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00503.proved (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01141 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X05 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01142 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K2347 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00509.proved (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01143 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X05 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01144 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2367 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00528.proved (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01145 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X05 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01146 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2467 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01147 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X05 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00085.proved (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01148 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K3467 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00598.proved (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl
