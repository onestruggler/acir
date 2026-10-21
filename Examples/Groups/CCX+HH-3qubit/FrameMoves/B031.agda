{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B031 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K1245 ; K1246 ; K1256 ; K1345 ; K1346 ; K1356 ; K1456 ; K2345 ; K2346 ; K2356 ; K2456 ; K3456 ; X07 ; X12 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00276 ; module MV00292 ; module MV00350 ; module MV00387 ; module MV00498)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00098 ; module MV00099 ; module MV00106 ; module MV00107 ; module MV00112)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00138 ; module MV00140 ; module MV00141 ; module MV00145 ; module MV00146 ; module MV00148 ; module MV00149 ; module MV00154 ; module MV00173 ; module MV00175 ; module MV00176 ; module MV00180 ; module MV00181 ; module MV00183 ; module MV00184 ; module MV00189 ; module MV00201 ; module MV00203 ; module MV00204 ; module MV00208 ; module MV00209 ; module MV00210 ; module MV00216 ; module MV00217 ; module MV00218 ; module MV00222 ; module MV00229 ; module MV00230 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00309)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00348 ; module MV00354 ; module MV00356)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00370 ; module MV00392)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00407 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00503)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00515 ; module MV00534)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00587)

module MV01186 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5) • K0123 ≈ K1245 • p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00348.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01187 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01188 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01189 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01190 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00368.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01191 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01192 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01193 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01194 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01195 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01196 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1356 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01197 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01198 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1456 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01199 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01200 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5) • K0123 ≈ K2345 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00498.proved (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01201 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01202 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2346 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00503.proved (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01203 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01204 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2356 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00515.proved (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01205 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01206 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K2456 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01207 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X07 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00099.proved (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01208 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K3456 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00587.proved (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01209 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • X45 ≈ X12 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00189.proved (MV00209.proved)))))) Eq.refl Eq.refl

module MV01210 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X12 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))) Eq.refl Eq.refl

module MV01211 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X12 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))) Eq.refl Eq.refl

module MV01212 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X12 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))) Eq.refl Eq.refl

module MV01213 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X12 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))) Eq.refl Eq.refl

module MV01214 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X12 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))) Eq.refl Eq.refl

module MV01215 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X12 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))) Eq.refl Eq.refl

module MV01216 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X12 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))) Eq.refl Eq.refl

module MV01217 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X12 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))))) Eq.refl Eq.refl

module MV01218 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X12 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00107.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))))) Eq.refl Eq.refl

module MV01219 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X12 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01220 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K3456 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00587.proved (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl
