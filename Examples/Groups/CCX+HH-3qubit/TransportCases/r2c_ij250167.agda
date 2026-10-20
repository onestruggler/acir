{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01429 as MV01429
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01430 as MV01430
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0167 ≈ K0167 • X25
proved = GL.•-cancelʳ {g = X25 • K0167} {g' = K0167 • X25} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01429.proved (MV01430.proved))) (trans (cong refl Base.proved) (move-product MV01430.proved (MV01429.proved))))
