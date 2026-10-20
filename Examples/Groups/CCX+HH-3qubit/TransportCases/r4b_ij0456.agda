{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; M0 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00671 as MV00671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02887 as MV02887
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02888 as MV02888
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X45 • K0456 ≈ M0 • K0456 • M0 • K0456 • M0
proved = GL.•-cancelʳ {g = X45 • K0456} {g' = M0 • K0456 • M0 • K0456 • M0} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02887.proved (MV00671.proved))) (trans (cong refl Base.proved) (move-product MV02888.proved (move-product MV00671.proved (move-product MV02888.proved (move-product MV00671.proved (MV02888.proved)))))))
