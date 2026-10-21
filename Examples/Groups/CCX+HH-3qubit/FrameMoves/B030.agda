{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B030 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1247 ; K1257 ; K1345 ; K1347 ; K1357 ; K1457 ; K2345 ; K2347 ; K2357 ; K2457 ; K3457 ; X06 ; X07 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00350 ; module MV00387 ; module MV00498)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00091 ; module MV00092)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00131 ; module MV00133 ; module MV00134 ; module MV00138 ; module MV00166 ; module MV00168 ; module MV00169 ; module MV00173 ; module MV00175 ; module MV00194 ; module MV00196 ; module MV00201 ; module MV00203 ; module MV00204 ; module MV00205 ; module MV00210 ; module MV00215 ; module MV00218 ; module MV00222)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00269 ; module MV00274 ; module MV00280 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00303 ; module MV00314 ; module MV00325 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00342 ; module MV00348 ; module MV00361 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00374 ; module MV00376 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00410 ; module MV00413)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00509)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00521 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592)

module MV01149 where

  proved : p (s0 • s1 • s2 • s3 • s5) • X45 ≈ X06 • p (s0 • s1 • s2 • s3 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00166.proved (move-compose MV00194.proved (move-compose MV00215.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01150 where

  proved : p (s0 • s1 • s2 • s3 • s5) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s5)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01151 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5) • X45 ≈ X06 • p (s0 • s1 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00166.proved (move-compose MV00194.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01152 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5) • K0123 ≈ K1235 • p (s0 • s1 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01153 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00166.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01154 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1237 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00342.proved (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01155 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s5) • X45 ≈ X06 • p (s0 • s1 • s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00166.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01156 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s5) • K0123 ≈ K1245 • p (s0 • s1 • s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00348.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01157 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00166.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01158 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1247 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00361.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01159 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00166.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01160 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1257 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00374.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01161 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5) • X45 ≈ X06 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01162 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01163 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01164 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1347 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01165 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01166 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1357 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01167 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01168 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1457 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01169 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5) • X45 ≈ X06 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01170 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5) • K0123 ≈ K2345 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00498.proved (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01171 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01172 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2347 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00509.proved (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01173 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01174 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2357 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00521.proved (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01175 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01176 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2457 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01177 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X06 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00092.proved (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01178 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K3457 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00592.proved (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01179 where

  proved : p (s0 • s1 • s2 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s1 • s2 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00173.proved (move-compose MV00201.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01180 where

  proved : p (s0 • s1 • s2 • s3 • s6 • s5) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01181 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s1 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00173.proved (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01182 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s6 • s5) • K0123 ≈ K1235 • p (s0 • s1 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01183 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00173.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01184 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1236 • p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01185 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl
