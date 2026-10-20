{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02123 as MV02123
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02124 as MV02124
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0167 ≈ K0167 • M4
proved = GL.•-cancelʳ {g = M4 • K0167} {g' = K0167 • M4} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02123.proved (MV02124.proved))) (trans (cong refl Base.proved) (move-product MV02124.proved (MV02123.proved))))
