{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; M1 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00688 as MV00688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02920 as MV02920
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02921 as MV02921
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X35 • K1356 ≈ M1 • K1356 • M1 • K1356 • M1
proved = GL.•-cancelʳ {g = X35 • K1356} {g' = M1 • K1356 • M1 • K1356 • M1} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02920.proved (MV00688.proved))) (trans (cong refl Base.proved) (move-product MV02921.proved (move-product MV00688.proved (move-product MV02921.proved (move-product MV00688.proved (MV02921.proved)))))))
