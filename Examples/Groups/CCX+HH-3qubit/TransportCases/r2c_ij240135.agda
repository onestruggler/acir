{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01393 as MV01393
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0135 ≈ K0135 • X24
proved = GL.•-cancelʳ {g = X24 • K0135} {g' = K0135 • X24} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV01393.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV00646.proved (MV01393.proved))))
