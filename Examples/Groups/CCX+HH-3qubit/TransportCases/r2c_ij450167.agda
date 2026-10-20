{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01633 as MV01633
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01634 as MV01634
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0167 ≈ K0167 • X45
proved = GL.•-cancelʳ {g = X45 • K0167} {g' = K0167 • X45} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01633.proved (MV01634.proved))) (trans (cong refl Base.proved) (move-product MV01634.proved (MV01633.proved))))
