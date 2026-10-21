{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B043 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0126 ; K0127 ; K0136 ; K0137 ; K0167 ; K0236 ; K0237 ; K0267 ; K0367 ; K0456 ; K1236 ; K1237 ; K1245 ; K1246 ; K1256 ; K1267 ; K1456 ; K2456 ; X37 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00199 ; module MV00200 ; module MV00203 ; module MV00206 ; module MV00207 ; module MV00208 ; module MV00210 ; module MV00211 ; module MV00216 ; module MV00217 ; module MV00218 ; module MV00220 ; module MV00221 ; module MV00222 ; module MV00223 ; module MV00224 ; module MV00228 ; module MV00229 ; module MV00230 ; module MV00234 ; module MV00235 ; module MV00236 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00280 ; module MV00282 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00309)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00342 ; module MV00348 ; module MV00354)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00370 ; module MV00381)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00534)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00005)

module MV01612 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X37 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01613 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0456 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01614 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00200.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01615 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1245 • p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00348.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01616 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00200.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01617 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01618 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00200.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01619 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00368.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01620 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X37 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01621 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1456 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01622 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X37 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01623 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2456 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01624 where

  proved : p (ε) • X45 ≈ X45 • p (ε)
  proved = by-assoc-and PE00005.proved Eq.refl Eq.refl

module MV01625 where

  proved : p (s5 • s4 • s3 • s4 • s5) • X45 ≈ X45 • p (s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01626 where

  proved : p (s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0126 • p (s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01627 where

  proved : p (s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X45 • p (s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01628 where

  proved : p (s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01629 where

  proved : p (s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X45 • p (s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01630 where

  proved : p (s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0136 • p (s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01631 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X45 • p (s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01632 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0137 • p (s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01633 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X45 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01634 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0167 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01635 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X45 • p (s1 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01636 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0236 • p (s1 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01637 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X45 • p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01638 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0237 • p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01639 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X45 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01640 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0267 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01641 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X45 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01642 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0367 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01643 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X45 • p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00207.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01644 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1236 • p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01645 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X45 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00207.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01646 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1237 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00342.proved (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01647 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X45 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01648 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1267 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00381.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl
