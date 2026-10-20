{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02191 as MV02191
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02192 as MV02192
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0167 ≈ K0167 • M5
proved = GL.•-cancelʳ {g = M5 • K0167} {g' = K0167 • M5} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02191.proved (MV02192.proved))) (trans (cong refl Base.proved) (move-product MV02192.proved (MV02191.proved))))
