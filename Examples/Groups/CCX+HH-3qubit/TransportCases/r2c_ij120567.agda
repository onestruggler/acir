{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00674 as MV00674
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01218 as MV01218
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K0567 ≈ K0567 • X12
proved = GL.•-cancelʳ {g = X12 • K0567} {g' = K0567 • X12} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01218.proved (MV00674.proved))) (trans (cong refl Base.proved) (move-product MV00674.proved (MV01218.proved))))
