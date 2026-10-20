{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02341567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K1567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02395 as MV02395
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0234 • K1567 ≈ K1567 • K0234
proved = GL.•-cancelʳ {g = K0234 • K1567} {g' = K1567 • K0234} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV00655.proved (MV02395.proved))) (trans (cong refl Base.proved) (move-product MV02395.proved (MV00655.proved))))
