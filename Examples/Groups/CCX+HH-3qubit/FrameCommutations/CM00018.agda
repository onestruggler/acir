{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00018 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (NK ; _•_ ; _≈_ ; axiom ; commute-product ; p ; r092 ; r093 ; s5 ; s6)
open K

proved : p (s6 • s5 • s6) • NK ≈ NK • p (s6 • s5 • s6)
proved = commute-product (axiom r093) (commute-product (axiom r092) (axiom r093))
