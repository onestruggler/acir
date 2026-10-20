{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01715 as MV01715
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01716 as MV01716
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0127 ≈ K0127 • X56
proved = GL.•-cancelʳ {g = X56 • K0127} {g' = K0127 • X56} {h = p (s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01715.proved (MV01716.proved))) (trans (cong refl Base.proved) (move-product MV01716.proved (MV01715.proved))))
