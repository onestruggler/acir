{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; M2 ; M6 ; X12 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00680 as MV00680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02711 as MV02711
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02712 as MV02712
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02713 as MV02713
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02714 as MV02714
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X12 • K1246 ≈ K1246 • X26 • M2 • M6
proved = GL.•-cancelʳ {g = X12 • K1246} {g' = K1246 • X26 • M2 • M6} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02711.proved (MV00680.proved))) (trans (cong refl Base.proved) (move-product MV00680.proved (move-product MV02712.proved (move-product MV02713.proved (MV02714.proved))))))
