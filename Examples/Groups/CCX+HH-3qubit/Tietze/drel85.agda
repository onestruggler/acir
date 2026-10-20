{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel85 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; K01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r025 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel63 as drel63

step0 : CCX12 • K01 ≈ K01 • K01 • CCX12 • K01
step0 = by-assoc-and (under (ε) (CCX12 • K01) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • CCX12 • K01 ≈ K01 • CCX02 • K01 • K01
step1 = by-assoc-and (under (K01) (K01) (drel63.proved)) Eq.refl Eq.refl

step2 : K01 • CCX02 • K01 • K01 ≈ K01 • CCX02
step2 = by-assoc-and (under (K01 • CCX02) (ε) (axiom r025)) Eq.refl Eq.refl

proved : CCX12 • K01 ≈ K01 • CCX02
proved = trans step0 (trans step1 (trans step2 (refl)))
