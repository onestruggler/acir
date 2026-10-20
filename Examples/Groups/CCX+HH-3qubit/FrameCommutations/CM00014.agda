{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00014 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (NK ; _•_ ; _≈_ ; axiom ; p ; r092 ; s5)
open K

proved : p (s5) • NK ≈ NK • p (s5)
proved = axiom r092
