{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 as MV00642
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01509 as MV01509
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0125 ≈ K0125 • X34
proved = GL.•-cancelʳ {g = X34 • K0125} {g' = K0125 • X34} {h = p (s4 • s3)}
  (trans (sym (move-product MV01509.proved (MV00642.proved))) (trans (cong refl Base.proved) (move-product MV00642.proved (MV01509.proved))))
