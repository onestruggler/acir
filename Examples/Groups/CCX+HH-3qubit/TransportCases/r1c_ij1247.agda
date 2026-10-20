{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij1247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K1247 • K1247 ≈ ε
proved = GL.•-cancelʳ {g = K1247 • K1247} {g' = ε} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00681.proved (MV00681.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
