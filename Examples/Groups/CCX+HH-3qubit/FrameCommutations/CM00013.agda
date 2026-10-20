{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00013 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (NK ; _•_ ; _≈_ ; axiom ; p ; r091 ; s4)
open K

proved : p (s4) • NK ≈ NK • p (s4)
proved = axiom r091
