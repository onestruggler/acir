{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij042357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; X04 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01112 as MV01112
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01113 as MV01113
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X04 • K2357 ≈ K2357 • X04
proved = GL.•-cancelʳ {g = X04 • K2357} {g' = K2357 • X04} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01112.proved (MV01113.proved))) (trans (cong refl Base.proved) (move-product MV01113.proved (MV01112.proved))))
