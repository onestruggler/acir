{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01381 as MV01381
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01382 as MV01382
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K0567 ≈ K0567 • X23
proved = GL.•-cancelʳ {g = X23 • K0567} {g' = K0567 • X23} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01381.proved (MV01382.proved))) (trans (cong refl Base.proved) (move-product MV01382.proved (MV01381.proved))))
