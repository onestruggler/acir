{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; M1 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00680 as MV00680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02904 as MV02904
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02905 as MV02905
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X24 • K1246 ≈ M1 • K1246 • M1 • K1246 • M1
proved = GL.•-cancelʳ {g = X24 • K1246} {g' = M1 • K1246 • M1 • K1246 • M1} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02904.proved (MV00680.proved))) (trans (cong refl Base.proved) (move-product MV02905.proved (move-product MV00680.proved (move-product MV02905.proved (move-product MV00680.proved (MV02905.proved)))))))
