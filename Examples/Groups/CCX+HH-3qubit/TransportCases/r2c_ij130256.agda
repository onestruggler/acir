{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01232 as MV01232
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K0256 ≈ K0256 • X13
proved = GL.•-cancelʳ {g = X13 • K0256} {g' = K0256 • X13} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01232.proved (MV00662.proved))) (trans (cong refl Base.proved) (move-product MV00662.proved (MV01232.proved))))
