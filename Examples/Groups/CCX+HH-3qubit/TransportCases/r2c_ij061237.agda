{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01153 as MV01153
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01154 as MV01154
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K1237 ≈ K1237 • X06
proved = GL.•-cancelʳ {g = X06 • K1237} {g' = K1237 • X06} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01153.proved (MV01154.proved))) (trans (cong refl Base.proved) (move-product MV01154.proved (MV01153.proved))))
