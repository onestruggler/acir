{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij162347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2347 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01331 as MV01331
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01332 as MV01332
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K2347 ≈ K2347 • X16
proved = GL.•-cancelʳ {g = X16 • K2347} {g' = K2347 • X16} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01331.proved (MV01332.proved))) (trans (cong refl Base.proved) (move-product MV01332.proved (MV01331.proved))))
