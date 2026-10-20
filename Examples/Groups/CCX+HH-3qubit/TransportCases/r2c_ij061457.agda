{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01167 as MV01167
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01168 as MV01168
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K1457 ≈ K1457 • X06
proved = GL.•-cancelʳ {g = X06 • K1457} {g' = K1457 • X06} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01167.proved (MV01168.proved))) (trans (cong refl Base.proved) (move-product MV01168.proved (MV01167.proved))))
