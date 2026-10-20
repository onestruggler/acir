{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij451367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01649 as MV01649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01650 as MV01650
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K1367 ≈ K1367 • X45
proved = GL.•-cancelʳ {g = X45 • K1367} {g' = K1367 • X45} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01649.proved (MV01650.proved))) (trans (cong refl Base.proved) (move-product MV01650.proved (MV01649.proved))))
