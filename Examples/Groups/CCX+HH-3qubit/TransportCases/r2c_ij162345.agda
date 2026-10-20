{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij162345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01329 as MV01329
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01330 as MV01330
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K2345 ≈ K2345 • X16
proved = GL.•-cancelʳ {g = X16 • K2345} {g' = K2345 • X16} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01329.proved (MV01330.proved))) (trans (cong refl Base.proved) (move-product MV01330.proved (MV01329.proved))))
