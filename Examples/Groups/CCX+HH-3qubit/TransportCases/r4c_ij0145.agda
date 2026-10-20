{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; X15 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00649 as MV00649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02588 as MV02588
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02971 as MV02971
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X45 • K0145 ≈ K0145 • X15
proved = GL.•-cancelʳ {g = X45 • K0145} {g' = K0145 • X15} {h = p (s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02971.proved (MV00649.proved))) (trans (cong refl Base.proved) (move-product MV00649.proved (MV02588.proved))))
