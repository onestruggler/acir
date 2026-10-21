{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (NK ; _•_ ; _≈_ ; axiom ; commute-product ; left-unit ; m0 ; p ; r085 ; r086 ; r087 ; r088 ; r089 ; r090 ; r091 ; r092 ; r093 ; right-unit ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K

module CM00012 where

  proved : p (ε) • NK ≈ NK • p (ε)
  proved = trans left-unit (sym right-unit)

module CM00013 where

  proved : p (s4) • NK ≈ NK • p (s4)
  proved = axiom r091

module CM00014 where

  proved : p (s5) • NK ≈ NK • p (s5)
  proved = axiom r092

module CM00015 where

  proved : p (s6) • NK ≈ NK • p (s6)
  proved = axiom r093

module CM00017 where

  proved : p (s6 • s5 • s4 • s5 • s6) • NK ≈ NK • p (s6 • s5 • s4 • s5 • s6)
  proved = commute-product (axiom r093) (commute-product (axiom r092) (commute-product (axiom r091) (commute-product (axiom r092) (axiom r093))))

module CM00000 where

  proved : p (ε) • m0 ≈ m0 • p (ε)
  proved = trans left-unit (sym right-unit)

module CM00001 where

  proved : p (s1) • m0 ≈ m0 • p (s1)
  proved = axiom r085

module CM00002 where

  proved : p (s2) • m0 ≈ m0 • p (s2)
  proved = axiom r086

module CM00003 where

  proved : p (s3) • m0 ≈ m0 • p (s3)
  proved = axiom r087

module CM00004 where

  proved : p (s4) • m0 ≈ m0 • p (s4)
  proved = axiom r088

module CM00005 where

  proved : p (s5) • m0 ≈ m0 • p (s5)
  proved = axiom r089

module CM00006 where

  proved : p (s6) • m0 ≈ m0 • p (s6)
  proved = axiom r090

module CM00007 where

  proved : p (s2 • s1 • s2) • m0 ≈ m0 • p (s2 • s1 • s2)
  proved = commute-product (axiom r086) (commute-product (axiom r085) (axiom r086))

module CM00008 where

  proved : p (s3 • s2 • s1 • s2 • s3) • m0 ≈ m0 • p (s3 • s2 • s1 • s2 • s3)
  proved = commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r085) (commute-product (axiom r086) (axiom r087))))

module CM00009 where

  proved : p (s4 • s3 • s2 • s1 • s2 • s3 • s4) • m0 ≈ m0 • p (s4 • s3 • s2 • s1 • s2 • s3 • s4)
  proved = commute-product (axiom r088) (commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r085) (commute-product (axiom r086) (commute-product (axiom r087) (axiom r088))))))

module CM00010 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5) • m0 ≈ m0 • p (s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5)
  proved = commute-product (axiom r089) (commute-product (axiom r088) (commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r085) (commute-product (axiom r086) (commute-product (axiom r087) (commute-product (axiom r088) (axiom r089))))))))

module CM00011 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6) • m0 ≈ m0 • p (s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6)
  proved = commute-product (axiom r090) (commute-product (axiom r089) (commute-product (axiom r088) (commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r085) (commute-product (axiom r086) (commute-product (axiom r087) (commute-product (axiom r088) (commute-product (axiom r089) (axiom r090))))))))))

module CM00016 where

  proved : p (s5 • s4 • s5) • NK ≈ NK • p (s5 • s4 • s5)
  proved = commute-product (axiom r092) (commute-product (axiom r091) (axiom r092))

module CM00018 where

  proved : p (s6 • s5 • s6) • NK ≈ NK • p (s6 • s5 • s6)
  proved = commute-product (axiom r093) (commute-product (axiom r092) (axiom r093))
