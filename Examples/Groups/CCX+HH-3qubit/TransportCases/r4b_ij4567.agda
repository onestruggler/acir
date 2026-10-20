{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij4567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; M4 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00631 as MV00631
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00632 as MV00632
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02962 as MV02962
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X56 • K4567 ≈ M4 • K4567 • M4 • K4567 • M4
proved = GL.•-cancelʳ {g = X56 • K4567} {g' = M4 • K4567 • M4 • K4567 • M4} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02962.proved (MV00632.proved))) (trans (cong refl Base.proved) (move-product MV00631.proved (move-product MV00632.proved (move-product MV00631.proved (move-product MV00632.proved (MV00631.proved)))))))
