{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00650 as MV00650
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01370 as MV01370
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K0146 ≈ K0146 • X23
proved = GL.•-cancelʳ {g = X23 • K0146} {g' = K0146 • X23} {h = p (s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01370.proved (MV00650.proved))) (trans (cong refl Base.proved) (move-product MV00650.proved (MV01370.proved))))
