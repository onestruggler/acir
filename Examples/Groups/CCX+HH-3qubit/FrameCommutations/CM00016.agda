{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00016 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (NK ; _•_ ; _≈_ ; axiom ; commute-product ; p ; r091 ; r092 ; s4 ; s5)
open K

proved : p (s5 • s4 • s5) • NK ≈ NK • p (s5 • s4 • s5)
proved = commute-product (axiom r092) (commute-product (axiom r091) (axiom r092))
