{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B050 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K2345 ; K2346 ; M0 ; M1 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00276 ; module MV00292 ; module MV00350 ; module MV00387 ; module MV00498)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00007 ; module MV00009 ; module MV00010 ; module MV00011 ; module MV00014 ; module MV00015 ; module MV00017 ; module MV00018 ; module MV00019 ; module MV00022 ; module MV00023 ; module MV00025 ; module MV00026 ; module MV00027 ; module MV00030 ; module MV00031 ; module MV00032 ; module MV00033 ; module MV00038 ; module MV00039)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00392)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00503)

module MV01919 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01920 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01921 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))) Eq.refl Eq.refl

module MV01922 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))) Eq.refl Eq.refl

module MV01923 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))) Eq.refl Eq.refl

module MV01924 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))))) Eq.refl Eq.refl

module MV01925 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))) Eq.refl Eq.refl

module MV01926 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))))) Eq.refl Eq.refl

module MV01927 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))))) Eq.refl Eq.refl

module MV01928 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))))))) Eq.refl Eq.refl

module MV01929 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M0 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))))) Eq.refl Eq.refl

module MV01930 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))))) Eq.refl Eq.refl

module MV01931 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))))))) Eq.refl Eq.refl

module MV01932 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))))))) Eq.refl Eq.refl

module MV01933 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M0 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))))))))) Eq.refl Eq.refl

module MV01934 where

  proved : p (s1 • s2 • s4 • s3) • M4 ≈ M1 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved)))) Eq.refl Eq.refl

module MV01935 where

  proved : p (s1 • s2 • s5 • s4 • s3) • M4 ≈ M1 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))) Eq.refl Eq.refl

module MV01936 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01937 where

  proved : p (s1 • s3 • s2 • s4 • s3) • M4 ≈ M1 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved))))) Eq.refl Eq.refl

module MV01938 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M1 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01939 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01940 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M1 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01941 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01942 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01943 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • M4 ≈ M1 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01944 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M1 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01945 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01946 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M1 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01947 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01948 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))) Eq.refl Eq.refl

module MV01949 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M1 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01950 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))) Eq.refl Eq.refl

module MV01951 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))))))) Eq.refl Eq.refl

module MV01952 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M1 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))))))) Eq.refl Eq.refl

module MV01953 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV01954 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4) • K0123 ≈ K2345 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00498.proved (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV01955 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV01956 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K2346 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00503.proved (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))) Eq.refl Eq.refl
