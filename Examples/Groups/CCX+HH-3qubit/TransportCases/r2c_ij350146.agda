{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01540 as MV01540
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01541 as MV01541
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0146 ≈ K0146 • X35
proved = GL.•-cancelʳ {g = X35 • K0146} {g' = K0146 • X35} {h = p (s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01540.proved (MV01541.proved))) (trans (cong refl Base.proved) (move-product MV01541.proved (MV01540.proved))))
