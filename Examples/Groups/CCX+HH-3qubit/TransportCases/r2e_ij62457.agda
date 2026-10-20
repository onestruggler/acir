{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij62457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2457 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02308 as MV02308
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02309 as MV02309
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K2457 ≈ K2457 • M6
proved = GL.•-cancelʳ {g = M6 • K2457} {g' = K2457 • M6} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02308.proved (MV02309.proved))) (trans (cong refl Base.proved) (move-product MV02309.proved (MV02308.proved))))
