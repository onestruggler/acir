{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; M2 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02950 as MV02950
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02951 as MV02951
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X46 • K2467 ≈ M2 • K2467 • M2 • K2467 • M2
proved = GL.•-cancelʳ {g = X46 • K2467} {g' = M2 • K2467 • M2 • K2467 • M2} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02950.proved (MV00703.proved))) (trans (cong refl Base.proved) (move-product MV02951.proved (move-product MV00703.proved (move-product MV02951.proved (move-product MV00703.proved (MV02951.proved)))))))
