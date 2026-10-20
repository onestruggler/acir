{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1247 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01071 as MV01071
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1247 ≈ K1247 • X03
proved = GL.•-cancelʳ {g = X03 • K1247} {g' = K1247 • X03} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01071.proved (MV00681.proved))) (trans (cong refl Base.proved) (move-product MV00681.proved (MV01071.proved))))
