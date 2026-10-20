{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01627 as MV01627
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01628 as MV01628
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0127 ≈ K0127 • X45
proved = GL.•-cancelʳ {g = X45 • K0127} {g' = K0127 • X45} {h = p (s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01627.proved (MV01628.proved))) (trans (cong refl Base.proved) (move-product MV01628.proved (MV01627.proved))))
