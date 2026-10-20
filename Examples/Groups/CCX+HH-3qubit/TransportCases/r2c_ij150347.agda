{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01293 as MV01293
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01294 as MV01294
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K0347 ≈ K0347 • X15
proved = GL.•-cancelʳ {g = X15 • K0347} {g' = K0347 • X15} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01293.proved (MV01294.proved))) (trans (cong refl Base.proved) (move-product MV01294.proved (MV01293.proved))))
