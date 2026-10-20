{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00666 as MV00666
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01210 as MV01210
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K0346 ≈ K0346 • X12
proved = GL.•-cancelʳ {g = X12 • K0346} {g' = K0346 • X12} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01210.proved (MV00666.proved))) (trans (cong refl Base.proved) (move-product MV00666.proved (MV01210.proved))))
