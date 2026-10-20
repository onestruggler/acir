{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01396 as MV01396
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01397 as MV01397
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0156 ≈ K0156 • X24
proved = GL.•-cancelʳ {g = X24 • K0156} {g' = K0156 • X24} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01396.proved (MV01397.proved))) (trans (cong refl Base.proved) (move-product MV01397.proved (MV01396.proved))))
