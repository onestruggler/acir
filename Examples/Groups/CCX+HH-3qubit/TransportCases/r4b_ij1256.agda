{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; M1 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02908 as MV02908
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02909 as MV02909
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X25 • K1256 ≈ M1 • K1256 • M1 • K1256 • M1
proved = GL.•-cancelʳ {g = X25 • K1256} {g' = M1 • K1256 • M1 • K1256 • M1} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02908.proved (MV00682.proved))) (trans (cong refl Base.proved) (move-product MV02909.proved (move-product MV00682.proved (move-product MV02909.proved (move-product MV00682.proved (MV02909.proved)))))))
