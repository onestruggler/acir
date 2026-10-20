{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; X36 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00666 as MV00666
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02656 as MV02656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02988 as MV02988
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X46 • K0346 ≈ K0346 • X36
proved = GL.•-cancelʳ {g = X46 • K0346} {g' = K0346 • X36} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02988.proved (MV00666.proved))) (trans (cong refl Base.proved) (move-product MV00666.proved (MV02656.proved))))
