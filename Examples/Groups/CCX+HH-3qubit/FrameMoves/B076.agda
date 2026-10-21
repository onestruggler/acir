{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B076 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K1345 ; K2345 ; NK ; X23 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00012)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00147 ; module MV00155 ; module MV00160 ; module MV00163 ; module MV00167 ; module MV00171 ; module MV00174 ; module MV00188 ; module MV00192 ; module MV00193 ; module MV00195 ; module MV00199 ; module MV00200 ; module MV00202 ; module MV00206 ; module MV00207 ; module MV00208 ; module MV00212 ; module MV00213 ; module MV00214 ; module MV00216 ; module MV00219 ; module MV00220 ; module MV00221 ; module MV00223 ; module MV00226 ; module MV00227 ; module MV00228 ; module MV00229 ; module MV00232 ; module MV00233 ; module MV00234 ; module MV00235 ; module MV00237 ; module MV00239 ; module MV00240 ; module MV00241 ; module MV00242 ; module MV00243)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00004 ; module PE00462 ; module PE00683 ; module PE00953)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B018 using (module PE01372)

module MV02999 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • X23 ≈ X36 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00193.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))) Eq.refl Eq.refl

module MV03000 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X37 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00200.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))) Eq.refl Eq.refl

module MV03001 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • X23 ≈ X45 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00207.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved)))))) Eq.refl Eq.refl

module MV03002 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X46 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00213.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))) Eq.refl Eq.refl

module MV03003 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X47 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00219.proved (move-compose MV00220.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))) Eq.refl Eq.refl

module MV03004 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00226.proved (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))) Eq.refl Eq.refl

module MV03005 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00232.proved (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))) Eq.refl Eq.refl

module MV03006 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))) Eq.refl Eq.refl

module MV03007 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • X23 ≈ X45 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved))))))) Eq.refl Eq.refl

module MV03008 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X46 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))) Eq.refl Eq.refl

module MV03009 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X47 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00219.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))) Eq.refl Eq.refl

module MV03010 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00226.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))) Eq.refl Eq.refl

module MV03011 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00232.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))) Eq.refl Eq.refl

module MV03012 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))) Eq.refl Eq.refl

module MV03013 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00226.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))) Eq.refl Eq.refl

module MV03014 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00232.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))) Eq.refl Eq.refl

module MV03015 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))))) Eq.refl Eq.refl

module MV03016 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))))) Eq.refl Eq.refl

module MV03017 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • X23 ≈ X45 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00155.proved (MV00147.proved)))))))) Eq.refl Eq.refl

module MV03018 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X46 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))) Eq.refl Eq.refl

module MV03019 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X47 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00220.proved (move-compose MV00219.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))) Eq.refl Eq.refl

module MV03020 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))) Eq.refl Eq.refl

module MV03021 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00233.proved (move-compose MV00232.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))) Eq.refl Eq.refl

module MV03022 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))))) Eq.refl Eq.refl

module MV03023 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))) Eq.refl Eq.refl

module MV03024 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00233.proved (move-compose MV00232.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))))) Eq.refl Eq.refl

module MV03025 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))))) Eq.refl Eq.refl

module MV03026 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))))))) Eq.refl Eq.refl

module MV03027 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X23 ≈ X56 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))))) Eq.refl Eq.refl

module MV03028 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X57 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00232.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))))) Eq.refl Eq.refl

module MV03029 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))))))) Eq.refl Eq.refl

module MV03030 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved))))))))))))))) Eq.refl Eq.refl

module MV03031 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X23 ≈ X67 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00171.proved (move-compose MV00163.proved (move-compose MV00155.proved (MV00147.proved)))))))))))))))) Eq.refl Eq.refl

module MV03032 where

  step0 : p (ε) • K1345 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)) PE00462.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ K1345 • p (ε)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00683.proved) Eq.refl Eq.refl

  proved : p (ε) • K1345 ≈ K1345 • p (ε)
  proved = trans step0 (trans step1 step2)

module MV03033 where

  step0 : p (ε) • K2345 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE01372.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2345 • p (ε)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00953.proved) Eq.refl Eq.refl

  proved : p (ε) • K2345 ≈ K2345 • p (ε)
  proved = trans step0 (trans step1 step2)

module MV03034 where

  step0 : p (ε) • K0124 ≈ p (s3) • p (ε) • NK • p (s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3)) PE00004.proved) Eq.refl Eq.refl

  step1 : p (s3) • p (ε) • NK • p (s3) ≈ p (s3) • NK • p (ε) • p (s3)
  step1 = by-assoc-and (under (p (s3)) (p (s3)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s3) • NK • p (ε) • p (s3) ≈ K0124 • p (ε)
  step2 = by-assoc-and (under (p (s3) • NK) (ε) PE00004.proved) Eq.refl Eq.refl

  proved : p (ε) • K0124 ≈ K0124 • p (ε)
  proved = trans step0 (trans step1 step2)
