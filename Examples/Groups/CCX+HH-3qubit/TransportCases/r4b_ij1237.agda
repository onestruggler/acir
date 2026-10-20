{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; M1 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00678 as MV00678
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02900 as MV02900
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02901 as MV02901
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X23 • K1237 ≈ M1 • K1237 • M1 • K1237 • M1
proved = GL.•-cancelʳ {g = X23 • K1237} {g' = M1 • K1237 • M1 • K1237 • M1} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02900.proved (MV00678.proved))) (trans (cong refl Base.proved) (move-product MV02901.proved (move-product MV00678.proved (move-product MV02901.proved (move-product MV00678.proved (MV02901.proved)))))))
