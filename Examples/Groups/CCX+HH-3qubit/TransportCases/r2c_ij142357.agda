{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij142357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01272 as MV01272
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01273 as MV01273
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K2357 ≈ K2357 • X14
proved = GL.•-cancelʳ {g = X14 • K2357} {g' = K2357 • X14} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01272.proved (MV01273.proved))) (trans (cong refl Base.proved) (move-product MV01273.proved (MV01272.proved))))
