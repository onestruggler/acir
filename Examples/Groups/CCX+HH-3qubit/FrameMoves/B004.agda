{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0234 ; K0235 ; K0236 ; K0237 ; NK ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00012 ; module CM00013 ; module CM00014 ; module CM00015 ; module CM00016 ; module CM00017)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00004 ; module PE00213)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00006 ; module PE00007)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B003 using (module PE00148 ; module PE00149 ; module PE00154 ; module PE00156 ; module PE00161 ; module PE00162 ; module PE00168 ; module PE00169 ; module PE00170)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B004 using (module PE00211 ; module PE00212 ; module PE00218 ; module PE00219 ; module PE00220 ; module PE00221 ; module PE00224 ; module PE00225 ; module PE00226 ; module PE00227 ; module PE00228 ; module PE00229 ; module PE00230 ; module PE00231 ; module PE00232 ; module PE00233 ; module PE00234 ; module PE00235 ; module PE00236 ; module PE00237 ; module PE00238 ; module PE00239 ; module PE00242 ; module PE00243 ; module PE00244 ; module PE00245 ; module PE00246 ; module PE00247 ; module PE00248 ; module PE00249 ; module PE00250 ; module PE00251 ; module PE00252)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B005 using (module PE00253 ; module PE00254 ; module PE00255 ; module PE00256 ; module PE00257 ; module PE00258 ; module PE00259 ; module PE00260 ; module PE00261 ; module PE00262 ; module PE00263 ; module PE00266 ; module PE00267 ; module PE00268 ; module PE00269 ; module PE00270 ; module PE00271 ; module PE00276 ; module PE00277 ; module PE00278 ; module PE00279 ; module PE00280 ; module PE00281)

module MV00247 where

  step0 : p (s5) • K0123 ≈ p (ε) • p (s5) • NK • p (ε)
  step0 = by-assoc-and (under (ε) (NK • p (ε)) PE00006.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s5) • NK • p (ε) ≈ p (ε) • NK • p (s5) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (ε) • NK • p (s5) • p (ε) ≈ K0123 • p (s5)
  step2 = by-assoc-and (under (p (ε) • NK) (ε) PE00006.proved) Eq.refl Eq.refl

  proved : p (s5) • K0123 ≈ K0123 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00248 where

  step0 : p (s6) • K0123 ≈ p (ε) • p (s6) • NK • p (ε)
  step0 = by-assoc-and (under (ε) (NK • p (ε)) PE00007.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s6) • NK • p (ε) ≈ p (ε) • NK • p (s6) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (ε) • NK • p (s6) • p (ε) ≈ K0123 • p (s6)
  step2 = by-assoc-and (under (p (ε) • NK) (ε) PE00007.proved) Eq.refl Eq.refl

  proved : p (s6) • K0123 ≈ K0123 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00249 where

  step0 : p (s2) • K0124 ≈ p (s2 • s3) • p (ε) • NK • p (s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3)) PE00211.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3) • p (ε) • NK • p (s3) ≈ p (s2 • s3) • NK • p (ε) • p (s3)
  step1 = by-assoc-and (under (p (s2 • s3)) (p (s3)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3) • NK • p (ε) • p (s3) ≈ K0134 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3) • NK) (ε) PE00212.proved) Eq.refl Eq.refl

  proved : p (s2) • K0124 ≈ K0134 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00250 where

  step0 : p (s3) • K0124 ≈ p (ε) • p (ε) • NK • p (s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3)) PE00213.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (ε) • NK • p (s3) ≈ p (ε) • NK • p (ε) • p (s3)
  step1 = by-assoc-and (under (p (ε)) (p (s3)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (ε) • NK • p (ε) • p (s3) ≈ K0123 • p (s3)
  step2 = by-assoc-and (under (p (ε) • NK) (ε) PE00004.proved) Eq.refl Eq.refl

  proved : p (s3) • K0124 ≈ K0123 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00252 where

  step0 : p (s5) • K0124 ≈ p (s3) • p (s5) • NK • p (s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3)) PE00148.proved) Eq.refl Eq.refl

  step1 : p (s3) • p (s5) • NK • p (s3) ≈ p (s3) • NK • p (s5) • p (s3)
  step1 = by-assoc-and (under (p (s3)) (p (s3)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s3) • NK • p (s5) • p (s3) ≈ K0124 • p (s5)
  step2 = by-assoc-and (under (p (s3) • NK) (ε) PE00148.proved) Eq.refl Eq.refl

  proved : p (s5) • K0124 ≈ K0124 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00253 where

  step0 : p (s6) • K0124 ≈ p (s3) • p (s6) • NK • p (s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3)) PE00149.proved) Eq.refl Eq.refl

  step1 : p (s3) • p (s6) • NK • p (s3) ≈ p (s3) • NK • p (s6) • p (s3)
  step1 = by-assoc-and (under (p (s3)) (p (s3)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s3) • NK • p (s6) • p (s3) ≈ K0124 • p (s6)
  step2 = by-assoc-and (under (p (s3) • NK) (ε) PE00149.proved) Eq.refl Eq.refl

  proved : p (s6) • K0124 ≈ K0124 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00256 where

  step0 : p (s4) • K0125 ≈ p (s3) • p (s4) • NK • p (s3 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3)) PE00154.proved) Eq.refl Eq.refl

  step1 : p (s3) • p (s4) • NK • p (s3 • s4 • s3) ≈ p (s3) • NK • p (s4) • p (s3 • s4 • s3)
  step1 = by-assoc-and (under (p (s3)) (p (s3 • s4 • s3)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s3) • NK • p (s4) • p (s3 • s4 • s3) ≈ K0124 • p (s4)
  step2 = by-assoc-and (under (p (s3) • NK) (ε) PE00154.proved) Eq.refl Eq.refl

  proved : p (s4) • K0125 ≈ K0124 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00258 where

  step0 : p (s6) • K0125 ≈ p (s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3)) PE00156.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3) ≈ p (s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s3)) (p (s3 • s4 • s3)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3) ≈ K0125 • p (s6)
  step2 = by-assoc-and (under (p (s3 • s4 • s3) • NK) (ε) PE00156.proved) Eq.refl Eq.refl

  proved : p (s6) • K0125 ≈ K0125 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00259 where

  step0 : p (s2) • K0126 ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3)) PE00218.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3) ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3) ≈ K0136 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00219.proved) Eq.refl Eq.refl

  proved : p (s2) • K0126 ≈ K0136 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00260 where

  step0 : p (s3) • K0126 ≈ p (s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3)) PE00220.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3) ≈ K0126 • p (s3)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00221.proved) Eq.refl Eq.refl

  proved : p (s3) • K0126 ≈ K0126 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00261 where

  step0 : p (s4) • K0126 ≈ p (s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3)) PE00161.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3) ≈ K0126 • p (s4)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00161.proved) Eq.refl Eq.refl

  proved : p (s4) • K0126 ≈ K0126 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00262 where

  step0 : p (s5) • K0126 ≈ p (s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3)) PE00162.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3) ≈ K0125 • p (s5)
  step2 = by-assoc-and (under (p (s3 • s4 • s3) • NK) (ε) PE00162.proved) Eq.refl Eq.refl

  proved : p (s5) • K0126 ≈ K0125 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00265 where

  step0 : p (s3) • K0127 ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) PE00224.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ K0127 • p (s3)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00225.proved) Eq.refl Eq.refl

  proved : p (s3) • K0127 ≈ K0127 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00266 where

  step0 : p (s4) • K0127 ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) PE00168.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ K0127 • p (s4)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00168.proved) Eq.refl Eq.refl

  proved : p (s4) • K0127 ≈ K0127 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00267 where

  step0 : p (s5) • K0127 ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) PE00169.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ K0127 • p (s5)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00169.proved) Eq.refl Eq.refl

  proved : p (s5) • K0127 ≈ K0127 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00268 where

  step0 : p (s6) • K0127 ≈ p (s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) PE00170.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ K0126 • p (s6)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00170.proved) Eq.refl Eq.refl

  proved : p (s6) • K0127 ≈ K0126 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00269 where

  step0 : p (s1) • K0134 ≈ p (s1 • s2 • s3) • p (ε) • NK • p (s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2)) PE00226.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3) • p (ε) • NK • p (s3 • s2) ≈ p (s1 • s2 • s3) • NK • p (ε) • p (s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3)) (p (s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3) • NK • p (ε) • p (s3 • s2) ≈ K0234 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3) • NK) (ε) PE00227.proved) Eq.refl Eq.refl

  proved : p (s1) • K0134 ≈ K0234 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00270 where

  step0 : p (s2) • K0134 ≈ p (s3) • p (ε) • NK • p (s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2)) PE00228.proved) Eq.refl Eq.refl

  step1 : p (s3) • p (ε) • NK • p (s3 • s2) ≈ p (s3) • NK • p (ε) • p (s3 • s2)
  step1 = by-assoc-and (under (p (s3)) (p (s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s3) • NK • p (ε) • p (s3 • s2) ≈ K0124 • p (s2)
  step2 = by-assoc-and (under (p (s3) • NK) (ε) PE00229.proved) Eq.refl Eq.refl

  proved : p (s2) • K0134 ≈ K0124 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00271 where

  step0 : p (s4) • K0134 ≈ p (s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2)) PE00230.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s2) ≈ p (s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3)) (p (s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s2) ≈ K0135 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3) • NK) (ε) PE00231.proved) Eq.refl Eq.refl

  proved : p (s4) • K0134 ≈ K0135 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00272 where

  step0 : p (s5) • K0134 ≈ p (s2 • s3) • p (s5) • NK • p (s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2)) PE00232.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3) • p (s5) • NK • p (s3 • s2) ≈ p (s2 • s3) • NK • p (s5) • p (s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3)) (p (s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3) • NK • p (s5) • p (s3 • s2) ≈ K0134 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3) • NK) (ε) PE00233.proved) Eq.refl Eq.refl

  proved : p (s5) • K0134 ≈ K0134 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00273 where

  step0 : p (s6) • K0134 ≈ p (s2 • s3) • p (s6) • NK • p (s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2)) PE00234.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3) • p (s6) • NK • p (s3 • s2) ≈ p (s2 • s3) • NK • p (s6) • p (s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3)) (p (s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3) • NK • p (s6) • p (s3 • s2) ≈ K0134 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3) • NK) (ε) PE00235.proved) Eq.refl Eq.refl

  proved : p (s6) • K0134 ≈ K0134 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00274 where

  step0 : p (s1) • K0135 ≈ p (s1 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2)) PE00236.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2) ≈ p (s1 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2) ≈ K0235 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00237.proved) Eq.refl Eq.refl

  proved : p (s1) • K0135 ≈ K0235 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00275 where

  step0 : p (s2) • K0135 ≈ p (s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2)) PE00238.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2) ≈ p (s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s3 • s4 • s3)) (p (s3 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2) ≈ K0125 • p (s2)
  step2 = by-assoc-and (under (p (s3 • s4 • s3) • NK) (ε) PE00239.proved) Eq.refl Eq.refl

  proved : p (s2) • K0135 ≈ K0125 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00277 where

  step0 : p (s4) • K0135 ≈ p (s2 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2)) PE00242.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2) ≈ p (s2 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3)) (p (s3 • s4 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2) ≈ K0134 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3) • NK) (ε) PE00243.proved) Eq.refl Eq.refl

  proved : p (s4) • K0135 ≈ K0134 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00278 where

  step0 : p (s5) • K0135 ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2)) PE00244.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2) ≈ K0136 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00245.proved) Eq.refl Eq.refl

  proved : p (s5) • K0135 ≈ K0136 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00279 where

  step0 : p (s6) • K0135 ≈ p (s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2)) PE00246.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2) ≈ K0135 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3) • NK) (ε) PE00247.proved) Eq.refl Eq.refl

  proved : p (s6) • K0135 ≈ K0135 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00280 where

  step0 : p (s1) • K0136 ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2)) PE00248.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ K0236 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00249.proved) Eq.refl Eq.refl

  proved : p (s1) • K0136 ≈ K0236 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00281 where

  step0 : p (s2) • K0136 ≈ p (s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2)) PE00250.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ K0126 • p (s2)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00251.proved) Eq.refl Eq.refl

  proved : p (s2) • K0136 ≈ K0126 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00282 where

  step0 : p (s3) • K0136 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2)) PE00252.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ K0146 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00253.proved) Eq.refl Eq.refl

  proved : p (s3) • K0136 ≈ K0146 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00283 where

  step0 : p (s4) • K0136 ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2)) PE00254.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ K0136 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00255.proved) Eq.refl Eq.refl

  proved : p (s4) • K0136 ≈ K0136 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00284 where

  step0 : p (s5) • K0136 ≈ p (s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2)) PE00256.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ K0135 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3) • NK) (ε) PE00257.proved) Eq.refl Eq.refl

  proved : p (s5) • K0136 ≈ K0135 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00285 where

  step0 : p (s6) • K0136 ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2)) PE00258.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2) ≈ K0137 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00259.proved) Eq.refl Eq.refl

  proved : p (s6) • K0136 ≈ K0137 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00286 where

  step0 : p (s1) • K0137 ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) PE00260.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ K0237 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00261.proved) Eq.refl Eq.refl

  proved : p (s1) • K0137 ≈ K0237 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00287 where

  step0 : p (s2) • K0137 ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) PE00262.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ K0127 • p (s2)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00263.proved) Eq.refl Eq.refl

  proved : p (s2) • K0137 ≈ K0127 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00289 where

  step0 : p (s4) • K0137 ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) PE00266.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ K0137 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00267.proved) Eq.refl Eq.refl

  proved : p (s4) • K0137 ≈ K0137 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00290 where

  step0 : p (s5) • K0137 ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) PE00268.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ K0137 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00269.proved) Eq.refl Eq.refl

  proved : p (s5) • K0137 ≈ K0137 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00291 where

  step0 : p (s6) • K0137 ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) PE00270.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ K0136 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00271.proved) Eq.refl Eq.refl

  proved : p (s6) • K0137 ≈ K0136 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00294 where

  step0 : p (s3) • K0145 ≈ p (s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2)) PE00276.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ K0135 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3) • NK) (ε) PE00277.proved) Eq.refl Eq.refl

  proved : p (s3) • K0145 ≈ K0135 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00295 where

  step0 : p (s5) • K0145 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2)) PE00278.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ K0146 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00279.proved) Eq.refl Eq.refl

  proved : p (s5) • K0145 ≈ K0146 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00296 where

  step0 : p (s6) • K0145 ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2)) PE00280.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ K0145 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00281.proved) Eq.refl Eq.refl

  proved : p (s6) • K0145 ≈ K0145 • p (s6)
  proved = trans step0 (trans step1 step2)
