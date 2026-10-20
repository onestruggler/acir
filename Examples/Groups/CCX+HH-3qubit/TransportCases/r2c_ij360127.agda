{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01568 as MV01568
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01569 as MV01569
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0127 ≈ K0127 • X36
proved = GL.•-cancelʳ {g = X36 • K0127} {g' = K0127 • X36} {h = p (s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01568.proved (MV01569.proved))) (trans (cong refl Base.proved) (move-product MV01569.proved (MV01568.proved))))
