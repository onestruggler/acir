{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01431 as MV01431
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01432 as MV01432
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0346 ≈ K0346 • X25
proved = GL.•-cancelʳ {g = X25 • K0346} {g' = K0346 • X25} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01431.proved (MV01432.proved))) (trans (cong refl Base.proved) (move-product MV01432.proved (MV01431.proved))))
