{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; X25 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00659 as MV00659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02628 as MV02628
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02981 as MV02981
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X45 • K0245 ≈ K0245 • X25
proved = GL.•-cancelʳ {g = X45 • K0245} {g' = K0245 • X25} {h = p (s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02981.proved (MV00659.proved))) (trans (cong refl Base.proved) (move-product MV00659.proved (MV02628.proved))))
