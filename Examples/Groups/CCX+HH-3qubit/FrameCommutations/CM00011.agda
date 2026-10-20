{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00011 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; axiom ; commute-product ; m0 ; p ; r085 ; r086 ; r087 ; r088 ; r089 ; r090 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K

proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6) • m0 ≈ m0 • p (s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6)
proved = commute-product (axiom r090) (commute-product (axiom r089) (commute-product (axiom r088) (commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r085) (commute-product (axiom r086) (commute-product (axiom r087) (commute-product (axiom r088) (commute-product (axiom r089) (axiom r090))))))))))
