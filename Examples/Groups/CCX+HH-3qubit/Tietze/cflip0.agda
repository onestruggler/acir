{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cflip0 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.cadd4 as cadd4
import Examples.Groups.CCX+HH-3qubit.Tietze.cadd5 as cadd5
import Examples.Groups.CCX+HH-3qubit.Tietze.cflip3 as cflip3

step0 : CX21 • CCX01 • CX21 ≈ CCX02 • CCX01 • CCX02
step0 = by-assoc-and (under (ε) (ε) (cadd4.proved)) Eq.refl Eq.refl

step1 : CCX02 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX01
step1 = by-assoc-and (under (ε) (ε) (cflip3.proved)) Eq.refl Eq.refl

step2 : CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12
step2 = by-assoc-and (under (ε) (ε) (sym (cadd5.proved))) Eq.refl Eq.refl

proved : CX21 • CCX01 • CX21 ≈ CX12 • CCX02 • CX12
proved = trans step0 (trans step1 (trans step2 (refl)))
