{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01395 as MV01395
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0137 ≈ K0137 • X24
proved = GL.•-cancelʳ {g = X24 • K0137} {g' = K0137 • X24} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01395.proved (MV00648.proved))) (trans (cong refl Base.proved) (move-product MV00648.proved (MV01395.proved))))
