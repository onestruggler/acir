{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; M1 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02898 as MV02898
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02899 as MV02899
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X23 • K1236 ≈ M1 • K1236 • M1 • K1236 • M1
proved = GL.•-cancelʳ {g = X23 • K1236} {g' = M1 • K1236 • M1 • K1236 • M1} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02898.proved (MV00677.proved))) (trans (cong refl Base.proved) (move-product MV02899.proved (move-product MV00677.proved (move-product MV02899.proved (move-product MV00677.proved (MV02899.proved)))))))
