{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij234567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01391 as MV01391
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01392 as MV01392
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K4567 ≈ K4567 • X23
proved = GL.•-cancelʳ {g = X23 • K4567} {g' = K4567 • X23} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01391.proved (MV01392.proved))) (trans (cong refl Base.proved) (move-product MV01392.proved (MV01391.proved))))
