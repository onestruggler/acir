{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01260 as MV01260
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01261 as MV01261
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0267 ≈ K0267 • X14
proved = GL.•-cancelʳ {g = X14 • K0267} {g' = K0267 • X14} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01260.proved (MV01261.proved))) (trans (cong refl Base.proved) (move-product MV01261.proved (MV01260.proved))))
