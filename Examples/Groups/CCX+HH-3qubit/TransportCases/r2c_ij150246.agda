{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01285 as MV01285
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01286 as MV01286
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K0246 ≈ K0246 • X15
proved = GL.•-cancelʳ {g = X15 • K0246} {g' = K0246 • X15} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01285.proved (MV01286.proved))) (trans (cong refl Base.proved) (move-product MV01286.proved (MV01285.proved))))
