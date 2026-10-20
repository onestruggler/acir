{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; X24 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02612 as MV02612
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02977 as MV02977
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X34 • K0234 ≈ K0234 • X24
proved = GL.•-cancelʳ {g = X34 • K0234} {g' = K0234 • X24} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV02977.proved (MV00655.proved))) (trans (cong refl Base.proved) (move-product MV00655.proved (MV02612.proved))))
