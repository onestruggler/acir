{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B040 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0156 ; K0157 ; K0167 ; K0256 ; K0257 ; K0267 ; K0567 ; K1256 ; K1257 ; K1267 ; K1346 ; K1356 ; K1456 ; K1567 ; K3456 ; X27 ; X34 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00172 ; module MV00175 ; module MV00179 ; module MV00180 ; module MV00183 ; module MV00184 ; module MV00189 ; module MV00199 ; module MV00200 ; module MV00201 ; module MV00203 ; module MV00207 ; module MV00208 ; module MV00209 ; module MV00210 ; module MV00211 ; module MV00216 ; module MV00217 ; module MV00218 ; module MV00220 ; module MV00221 ; module MV00222 ; module MV00223 ; module MV00224 ; module MV00228 ; module MV00229 ; module MV00230 ; module MV00234 ; module MV00235 ; module MV00236 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00370 ; module MV00374 ; module MV00381 ; module MV00392)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00407 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00534)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00587)

module MV01501 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X27 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01502 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01503 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X27 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01504 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1356 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01505 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X27 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01506 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1456 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01507 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X27 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01508 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K3456 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00587.proved (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl

module MV01509 where

  proved : p (s4 • s3) • X45 ≈ X34 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00189.proved (MV00209.proved)) Eq.refl Eq.refl

module MV01510 where

  proved : p (s5 • s4 • s3) • X45 ≈ X34 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))) Eq.refl Eq.refl

module MV01511 where

  proved : p (s6 • s5 • s4 • s3) • X45 ≈ X34 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))) Eq.refl Eq.refl

module MV01512 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01513 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0156 • p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01514 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01515 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0157 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01516 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01517 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0167 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01518 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01519 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0256 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01520 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01521 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0257 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01522 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01523 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0267 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01524 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X34 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01525 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0567 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl

module MV01526 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00180.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01527 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00368.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01528 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00180.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01529 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1257 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00374.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01530 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X34 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00180.proved (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01531 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1267 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00381.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01532 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X34 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))))) Eq.refl Eq.refl

module MV01533 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1567 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))))) Eq.refl Eq.refl

module MV01534 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X34 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))))) Eq.refl Eq.refl
