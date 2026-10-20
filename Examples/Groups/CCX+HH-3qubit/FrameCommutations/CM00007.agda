{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00007 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; axiom ; commute-product ; m0 ; p ; r085 ; r086 ; s1 ; s2)
open K

proved : p (s2 • s1 • s2) • m0 ≈ m0 • p (s2 • s1 • s2)
proved = commute-product (axiom r086) (commute-product (axiom r085) (axiom r086))
