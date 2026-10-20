{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij021456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00691 as MV00691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01055 as MV01055
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X02 • K1456 ≈ K1456 • X02
proved = GL.•-cancelʳ {g = X02 • K1456} {g' = K1456 • X02} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01055.proved (MV00691.proved))) (trans (cong refl Base.proved) (move-product MV00691.proved (MV01055.proved))))
