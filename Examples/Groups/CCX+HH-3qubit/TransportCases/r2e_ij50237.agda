{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02197 as MV02197
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02198 as MV02198
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0237 ≈ K0237 • M5
proved = GL.•-cancelʳ {g = M5 • K0237} {g' = K0237 • M5} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02197.proved (MV02198.proved))) (trans (cong refl Base.proved) (move-product MV02198.proved (MV02197.proved))))
