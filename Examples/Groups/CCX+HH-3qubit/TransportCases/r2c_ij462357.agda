{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij462357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01679 as MV01679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01680 as MV01680
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K2357 ≈ K2357 • X46
proved = GL.•-cancelʳ {g = X46 • K2357} {g' = K2357 • X46} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01679.proved (MV01680.proved))) (trans (cong refl Base.proved) (move-product MV01680.proved (MV01679.proved))))
