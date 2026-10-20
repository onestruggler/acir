{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; NK ; _≈_ ; by-assoc ; module Eq)
open K

proved : NK ≈ K0123
proved = by-assoc Eq.refl
