{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; X27 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02716 as MV02716
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03003 as MV03003
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X47 • K1247 ≈ K1247 • X27
proved = GL.•-cancelʳ {g = X47 • K1247} {g' = K1247 • X27} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03003.proved (MV00681.proved))) (trans (cong refl Base.proved) (move-product MV00681.proved (MV02716.proved))))
