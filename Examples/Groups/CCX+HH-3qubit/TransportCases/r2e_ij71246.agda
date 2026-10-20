{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij71246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02359 as MV02359
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02360 as MV02360
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K1246 ≈ K1246 • M7
proved = GL.•-cancelʳ {g = M7 • K1246} {g' = K1246 • M7} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02359.proved (MV02360.proved))) (trans (cong refl Base.proved) (move-product MV02360.proved (MV02359.proved))))
