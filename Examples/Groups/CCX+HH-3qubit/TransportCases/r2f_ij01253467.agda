{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01253467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; K3467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00642 as MV00642
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02382 as MV02382
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0125 • K3467 ≈ K3467 • K0125
proved = GL.•-cancelʳ {g = K0125 • K3467} {g' = K3467 • K0125} {h = p (s4 • s3)}
  (trans (sym (move-product MV00642.proved (MV02382.proved))) (trans (cong refl Base.proved) (move-product MV02382.proved (MV00642.proved))))
