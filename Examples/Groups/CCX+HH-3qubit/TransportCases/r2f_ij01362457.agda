{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01362457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; K2457 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00647 as MV00647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02387 as MV02387
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0136 • K2457 ≈ K2457 • K0136
proved = GL.•-cancelʳ {g = K0136 • K2457} {g' = K2457 • K0136} {h = p (s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00647.proved (MV02387.proved))) (trans (cong refl Base.proved) (move-product MV02387.proved (MV00647.proved))))
