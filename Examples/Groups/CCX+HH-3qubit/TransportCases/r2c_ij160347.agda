{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01323 as MV01323
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01324 as MV01324
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K0347 ≈ K0347 • X16
proved = GL.•-cancelʳ {g = X16 • K0347} {g' = K0347 • X16} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01323.proved (MV01324.proved))) (trans (cong refl Base.proved) (move-product MV01324.proved (MV01323.proved))))
