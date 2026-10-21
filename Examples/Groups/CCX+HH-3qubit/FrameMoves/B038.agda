{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B038 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0134 ; K0135 ; K0137 ; K0145 ; K0147 ; K0157 ; K0167 ; K0345 ; K0346 ; K0347 ; K0367 ; K0467 ; K1346 ; K1347 ; K1367 ; K1467 ; K3467 ; X25 ; X26 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00350 ; module MV00383 ; module MV00420)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00158 ; module MV00161 ; module MV00168 ; module MV00169 ; module MV00170 ; module MV00185 ; module MV00186 ; module MV00187 ; module MV00191 ; module MV00193 ; module MV00194 ; module MV00196 ; module MV00197 ; module MV00203 ; module MV00204 ; module MV00205 ; module MV00207 ; module MV00208 ; module MV00209 ; module MV00210 ; module MV00211 ; module MV00214 ; module MV00215 ; module MV00216 ; module MV00217 ; module MV00218 ; module MV00222 ; module MV00223 ; module MV00224 ; module MV00225 ; module MV00228 ; module MV00229 ; module MV00230 ; module MV00235 ; module MV00236 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00303)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00392 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00417)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00598)

module MV01427 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X25 • p (s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01428 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01429 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X25 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01430 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0167 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01431 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X25 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01432 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0346 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01433 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X25 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01434 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0347 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01435 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X25 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01436 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0367 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01437 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X25 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01438 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0467 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01439 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X25 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01440 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01441 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X25 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01442 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1347 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01443 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X25 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01444 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1367 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01445 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X25 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01446 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1467 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01447 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X25 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))))) Eq.refl Eq.refl

module MV01448 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K3467 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00598.proved (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))))) Eq.refl Eq.refl

module MV01449 where

  proved : p (s2 • s3 • s5) • X45 ≈ X26 • p (s2 • s3 • s5)
  proved = by-assoc-and (move-compose MV00194.proved (move-compose MV00215.proved (MV00210.proved))) Eq.refl Eq.refl

module MV01450 where

  proved : p (s2 • s3 • s5) • K0123 ≈ K0134 • p (s2 • s3 • s5)
  proved = by-assoc-and (move-compose MV00249.proved (move-compose MV00245.proved (MV00247.proved))) Eq.refl Eq.refl

module MV01451 where

  proved : p (s2 • s4 • s3 • s5) • X45 ≈ X26 • p (s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00194.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))) Eq.refl Eq.refl

module MV01452 where

  proved : p (s2 • s4 • s3 • s5) • K0123 ≈ K0135 • p (s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))) Eq.refl Eq.refl

module MV01453 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X26 • p (s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01454 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0137 • p (s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01455 where

  proved : p (s3 • s2 • s4 • s3 • s5) • X45 ≈ X26 • p (s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01456 where

  proved : p (s3 • s2 • s4 • s3 • s5) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01457 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X26 • p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01458 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01459 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X26 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01460 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0157 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01461 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5) • X45 ≈ X26 • p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01462 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01463 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X26 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl
