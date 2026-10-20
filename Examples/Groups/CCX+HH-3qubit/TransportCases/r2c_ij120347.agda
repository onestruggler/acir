{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00667 as MV00667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01211 as MV01211
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K0347 ≈ K0347 • X12
proved = GL.•-cancelʳ {g = X12 • K0347} {g' = K0347 • X12} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01211.proved (MV00667.proved))) (trans (cong refl Base.proved) (move-product MV00667.proved (MV01211.proved))))
