{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01400 as MV01400
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01401 as MV01401
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0167 ≈ K0167 • X24
proved = GL.•-cancelʳ {g = X24 • K0167} {g' = K0167 • X24} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01400.proved (MV01401.proved))) (trans (cong refl Base.proved) (move-product MV01401.proved (MV01400.proved))))
