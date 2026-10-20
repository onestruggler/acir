{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01661 as MV01661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01662 as MV01662
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K0157 ≈ K0157 • X46
proved = GL.•-cancelʳ {g = X46 • K0157} {g' = K0157 • X46} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01661.proved (MV01662.proved))) (trans (cong refl Base.proved) (move-product MV01662.proved (MV01661.proved))))
