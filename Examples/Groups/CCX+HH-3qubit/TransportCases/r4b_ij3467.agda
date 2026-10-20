{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij3467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; M3 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00707 as MV00707
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02958 as MV02958
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02959 as MV02959
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X46 • K3467 ≈ M3 • K3467 • M3 • K3467 • M3
proved = GL.•-cancelʳ {g = X46 • K3467} {g' = M3 • K3467 • M3 • K3467 • M3} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02958.proved (MV00707.proved))) (trans (cong refl Base.proved) (move-product MV02959.proved (move-product MV00707.proved (move-product MV02959.proved (move-product MV00707.proved (MV02959.proved)))))))
