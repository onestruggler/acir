{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij4567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; M5 ; M7 ; X45 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00632 as MV00632
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02827 as MV02827
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02828 as MV02828
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02829 as MV02829
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02830 as MV02830
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X45 • K4567 ≈ K4567 • X57 • M5 • M7
proved = GL.•-cancelʳ {g = X45 • K4567} {g' = K4567 • X57 • M5 • M7} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02827.proved (MV00632.proved))) (trans (cong refl Base.proved) (move-product MV00632.proved (move-product MV02828.proved (move-product MV02829.proved (MV02830.proved))))))
