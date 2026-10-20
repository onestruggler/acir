{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01069 as MV01069
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1245 ≈ K1245 • X03
proved = GL.•-cancelʳ {g = X03 • K1245} {g' = K1245 • X03} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01069.proved (MV00679.proved))) (trans (cong refl Base.proved) (move-product MV00679.proved (MV01069.proved))))
