{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00015 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (NK ; _•_ ; _≈_ ; axiom ; p ; r093 ; s6)
open K

proved : p (s6) • NK ≈ NK • p (s6)
proved = axiom r093
