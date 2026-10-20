{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00671 as MV00671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01215 as MV01215
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K0456 ≈ K0456 • X12
proved = GL.•-cancelʳ {g = X12 • K0456} {g' = K0456 • X12} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01215.proved (MV00671.proved))) (trans (cong refl Base.proved) (move-product MV00671.proved (MV01215.proved))))
