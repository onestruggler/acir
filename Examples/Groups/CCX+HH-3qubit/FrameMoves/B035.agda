{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B035 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0234 ; K0235 ; K0236 ; K0245 ; K0246 ; K0256 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0456 ; K0457 ; K2345 ; K2347 ; K2357 ; K2457 ; K3457 ; X16 ; X17 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00350 ; module MV00387 ; module MV00498)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00133 ; module MV00134 ; module MV00140 ; module MV00141 ; module MV00165 ; module MV00166 ; module MV00168 ; module MV00169 ; module MV00173 ; module MV00175 ; module MV00176 ; module MV00193 ; module MV00194 ; module MV00196 ; module MV00201 ; module MV00203 ; module MV00204 ; module MV00205 ; module MV00210 ; module MV00214 ; module MV00215 ; module MV00216 ; module MV00218 ; module MV00222 ; module MV00223 ; module MV00224 ; module MV00225 ; module MV00229 ; module MV00230 ; module MV00235 ; module MV00236 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00269 ; module MV00274 ; module MV00280 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407 ; module MV00410 ; module MV00413)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00509)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00521 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592)

module MV01322 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01323 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X16 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01324 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0347 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01325 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X16 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01326 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0357 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01327 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X16 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01328 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01329 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5) • X45 ≈ X16 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01330 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5) • K0123 ≈ K2345 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00498.proved (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01331 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X16 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01332 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K2347 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00509.proved (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01333 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X16 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01334 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K2357 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00521.proved (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01335 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X16 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01336 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K2457 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01337 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X16 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01338 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K3457 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00592.proved (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl

module MV01339 where

  proved : p (s1 • s2 • s3 • s6 • s5) • X45 ≈ X17 • p (s1 • s2 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00173.proved (move-compose MV00201.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01340 where

  proved : p (s1 • s2 • s3 • s6 • s5) • K0123 ≈ K0234 • p (s1 • s2 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01341 where

  proved : p (s1 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s1 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00173.proved (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01342 where

  proved : p (s1 • s2 • s4 • s3 • s6 • s5) • K0123 ≈ K0235 • p (s1 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01343 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s1 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00173.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01344 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0236 • p (s1 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01345 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01346 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s6 • s5) • K0123 ≈ K0245 • p (s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01347 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01348 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0246 • p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01349 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01350 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0256 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01351 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01352 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01353 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01354 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0346 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01355 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01356 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0356 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01357 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X17 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01358 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0456 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl
