{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01155 as MV01155
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01156 as MV01156
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K1245 ≈ K1245 • X06
proved = GL.•-cancelʳ {g = X06 • K1245} {g' = K1245 • X06} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01155.proved (MV01156.proved))) (trans (cong refl Base.proved) (move-product MV01156.proved (MV01155.proved))))
