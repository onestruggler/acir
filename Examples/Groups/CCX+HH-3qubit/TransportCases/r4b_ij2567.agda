{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2567 ; M2 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00704 as MV00704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02952 as MV02952
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02953 as MV02953
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X56 • K2567 ≈ M2 • K2567 • M2 • K2567 • M2
proved = GL.•-cancelʳ {g = X56 • K2567} {g' = M2 • K2567 • M2 • K2567 • M2} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02952.proved (MV00704.proved))) (trans (cong refl Base.proved) (move-product MV02953.proved (move-product MV00704.proved (move-product MV02953.proved (move-product MV00704.proved (MV02953.proved)))))))
