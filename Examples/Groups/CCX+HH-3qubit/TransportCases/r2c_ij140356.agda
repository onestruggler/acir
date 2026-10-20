{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01262 as MV01262
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01263 as MV01263
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0356 ≈ K0356 • X14
proved = GL.•-cancelʳ {g = X14 • K0356} {g' = K0356 • X14} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01262.proved (MV01263.proved))) (trans (cong refl Base.proved) (move-product MV01263.proved (MV01262.proved))))
