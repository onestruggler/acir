{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01216 as MV01216
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K0457 ≈ K0457 • X12
proved = GL.•-cancelʳ {g = X12 • K0457} {g' = K0457 • X12} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01216.proved (MV00672.proved))) (trans (cong refl Base.proved) (move-product MV00672.proved (MV01216.proved))))
