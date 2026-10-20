{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02187 as MV02187
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02188 as MV02188
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0146 ≈ K0146 • M5
proved = GL.•-cancelʳ {g = M5 • K0146} {g' = K0146 • M5} {h = p (s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02187.proved (MV02188.proved))) (trans (cong refl Base.proved) (move-product MV02188.proved (MV02187.proved))))
