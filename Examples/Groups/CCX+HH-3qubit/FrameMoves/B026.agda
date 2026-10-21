{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B026 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; X01 ; X02 ; X12 ; X45 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00057 ; module MV00058 ; module MV00063 ; module MV00104 ; module MV00105 ; module MV00106 ; module MV00107 ; module MV00112 ; module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00129 ; module MV00137 ; module MV00139 ; module MV00146 ; module MV00148 ; module MV00149 ; module MV00154 ; module MV00174 ; module MV00181 ; module MV00183 ; module MV00184 ; module MV00189 ; module MV00202 ; module MV00209 ; module MV00223 ; module MV00237 ; module MV00239 ; module MV00240 ; module MV00241 ; module MV00242 ; module MV00243 ; module MV00244)

module MV01020 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X57 • p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))))))) Eq.refl Eq.refl

module MV01021 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))))))) Eq.refl Eq.refl

module MV01022 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X67 • p (s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV01023 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M0 • p (s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV01024 where

  proved : p (s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X67 • p (s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV01025 where

  proved : p (s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV01026 where

  proved : p (s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X67 • p (s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV01027 where

  proved : p (s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV01028 where

  proved : p (s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X67 • p (s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))) Eq.refl Eq.refl

module MV01029 where

  proved : p (s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))) Eq.refl Eq.refl

module MV01030 where

  proved : p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X67 • p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))))) Eq.refl Eq.refl

module MV01031 where

  proved : p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))))) Eq.refl Eq.refl

module MV01032 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X67 • p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))))) Eq.refl Eq.refl

module MV01033 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))))) Eq.refl Eq.refl

module MV01034 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00189.proved (MV00209.proved)))))))) Eq.refl Eq.refl

module MV01035 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))) Eq.refl Eq.refl

module MV01036 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))) Eq.refl Eq.refl

module MV01037 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))) Eq.refl Eq.refl

module MV01038 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))))) Eq.refl Eq.refl

module MV01039 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))))) Eq.refl Eq.refl

module MV01040 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))))) Eq.refl Eq.refl

module MV01041 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))))) Eq.refl Eq.refl

module MV01042 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))))))) Eq.refl Eq.refl

module MV01043 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00107.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))))))) Eq.refl Eq.refl

module MV01044 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X01 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00057.proved (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))))) Eq.refl Eq.refl

module MV01045 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00057.proved (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))))))) Eq.refl Eq.refl

module MV01046 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00057.proved (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))))))) Eq.refl Eq.refl

module MV01047 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00057.proved (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00107.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))))))))) Eq.refl Eq.refl

module MV01048 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X01 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00063.proved (move-compose MV00104.proved (move-compose MV00107.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))))))))))) Eq.refl Eq.refl

module MV01049 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • X45 ≈ X02 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00189.proved (MV00209.proved))))))) Eq.refl Eq.refl

module MV01050 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X02 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))) Eq.refl Eq.refl

module MV01051 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X02 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00104.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))) Eq.refl Eq.refl
