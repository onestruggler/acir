{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01402 as MV01402
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01403 as MV01403
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0356 ≈ K0356 • X24
proved = GL.•-cancelʳ {g = X24 • K0356} {g' = K0356 • X24} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01402.proved (MV01403.proved))) (trans (cong refl Base.proved) (move-product MV01403.proved (MV01402.proved))))
