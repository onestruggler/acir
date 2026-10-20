{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2567 ; M5 ; M7 ; X25 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00704 as MV00704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02807 as MV02807
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02808 as MV02808
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02809 as MV02809
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02810 as MV02810
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X25 • K2567 ≈ K2567 • X57 • M5 • M7
proved = GL.•-cancelʳ {g = X25 • K2567} {g' = K2567 • X57 • M5 • M7} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02807.proved (MV00704.proved))) (trans (cong refl Base.proved) (move-product MV00704.proved (move-product MV02808.proved (move-product MV02809.proved (MV02810.proved))))))
