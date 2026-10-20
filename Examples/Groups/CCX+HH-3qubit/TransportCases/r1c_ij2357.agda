{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij2357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00699 as MV00699
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K2357 • K2357 ≈ ε
proved = GL.•-cancelʳ {g = K2357 • K2357} {g' = ε} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00699.proved (MV00699.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
