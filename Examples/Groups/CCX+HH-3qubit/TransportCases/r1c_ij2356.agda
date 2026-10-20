{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij2356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00698 as MV00698
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K2356 • K2356 ≈ ε
proved = GL.•-cancelʳ {g = K2356 • K2356} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00698.proved (MV00698.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
