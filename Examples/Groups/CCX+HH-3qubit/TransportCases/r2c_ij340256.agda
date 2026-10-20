{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01518 as MV01518
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01519 as MV01519
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0256 ≈ K0256 • X34
proved = GL.•-cancelʳ {g = X34 • K0256} {g' = K0256 • X34} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01518.proved (MV01519.proved))) (trans (cong refl Base.proved) (move-product MV01519.proved (MV01518.proved))))
