{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01725 as MV01725
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01726 as MV01726
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0237 ≈ K0237 • X56
proved = GL.•-cancelʳ {g = X56 • K0237} {g' = K0237 • X56} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01725.proved (MV01726.proved))) (trans (cong refl Base.proved) (move-product MV01726.proved (MV01725.proved))))
