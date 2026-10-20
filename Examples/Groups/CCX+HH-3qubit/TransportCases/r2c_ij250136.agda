{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01421 as MV01421
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01422 as MV01422
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0136 ≈ K0136 • X25
proved = GL.•-cancelʳ {g = X25 • K0136} {g' = K0136 • X25} {h = p (s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01421.proved (MV01422.proved))) (trans (cong refl Base.proved) (move-product MV01422.proved (MV01421.proved))))
