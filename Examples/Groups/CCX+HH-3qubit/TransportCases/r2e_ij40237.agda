{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02129 as MV02129
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02130 as MV02130
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0237 ≈ K0237 • M4
proved = GL.•-cancelʳ {g = M4 • K0237} {g' = K0237 • M4} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02129.proved (MV02130.proved))) (trans (cong refl Base.proved) (move-product MV02130.proved (MV02129.proved))))
