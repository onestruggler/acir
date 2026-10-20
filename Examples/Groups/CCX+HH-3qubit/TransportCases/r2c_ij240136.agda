{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00647 as MV00647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01394 as MV01394
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0136 ≈ K0136 • X24
proved = GL.•-cancelʳ {g = X24 • K0136} {g' = K0136 • X24} {h = p (s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01394.proved (MV00647.proved))) (trans (cong refl Base.proved) (move-product MV00647.proved (MV01394.proved))))
