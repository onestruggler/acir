{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00008 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; axiom ; commute-product ; m0 ; p ; r085 ; r086 ; r087 ; s1 ; s2 ; s3)
open K

proved : p (s3 • s2 • s1 • s2 • s3) • m0 ≈ m0 • p (s3 • s2 • s1 • s2 • s3)
proved = commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r085) (commute-product (axiom r086) (axiom r087))))
