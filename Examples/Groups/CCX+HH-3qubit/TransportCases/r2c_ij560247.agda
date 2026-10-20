{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01727 as MV01727
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01728 as MV01728
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0247 ≈ K0247 • X56
proved = GL.•-cancelʳ {g = X56 • K0247} {g' = K0247 • X56} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01727.proved (MV01728.proved))) (trans (cong refl Base.proved) (move-product MV01728.proved (MV01727.proved))))
