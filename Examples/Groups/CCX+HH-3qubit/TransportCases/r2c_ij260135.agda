{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01451 as MV01451
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01452 as MV01452
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K0135 ≈ K0135 • X26
proved = GL.•-cancelʳ {g = X26 • K0135} {g' = K0135 • X26} {h = p (s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01451.proved (MV01452.proved))) (trans (cong refl Base.proved) (move-product MV01452.proved (MV01451.proved))))
