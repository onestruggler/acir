{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; M0 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00657 as MV00657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02859 as MV02859
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02860 as MV02860
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X23 • K0236 ≈ M0 • K0236 • M0 • K0236 • M0
proved = GL.•-cancelʳ {g = X23 • K0236} {g' = M0 • K0236 • M0 • K0236 • M0} {h = p (s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02859.proved (MV00657.proved))) (trans (cong refl Base.proved) (move-product MV02860.proved (move-product MV00657.proved (move-product MV02860.proved (move-product MV00657.proved (MV02860.proved)))))))
