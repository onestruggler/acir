{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; M1 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00694 as MV00694
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02932 as MV02932
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02933 as MV02933
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X56 • K1567 ≈ M1 • K1567 • M1 • K1567 • M1
proved = GL.•-cancelʳ {g = X56 • K1567} {g' = M1 • K1567 • M1 • K1567 • M1} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02932.proved (MV00694.proved))) (trans (cong refl Base.proved) (move-product MV02933.proved (move-product MV00694.proved (move-product MV02933.proved (move-product MV00694.proved (MV02933.proved)))))))
