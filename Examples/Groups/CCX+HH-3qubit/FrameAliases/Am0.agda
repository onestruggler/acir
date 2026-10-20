{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _≈_ ; by-assoc ; m0 ; module Eq)
open K

proved : m0 ≈ M0
proved = by-assoc Eq.refl
