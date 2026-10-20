{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01566 as MV01566
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01567 as MV01567
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0125 ≈ K0125 • X36
proved = GL.•-cancelʳ {g = X36 • K0125} {g' = K0125 • X36} {h = p (s4 • s3 • s5)}
  (trans (sym (move-product MV01566.proved (MV01567.proved))) (trans (cong refl Base.proved) (move-product MV01567.proved (MV01566.proved))))
