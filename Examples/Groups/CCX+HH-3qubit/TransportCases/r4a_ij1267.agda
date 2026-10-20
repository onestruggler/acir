{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; M2 ; M7 ; X12 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00684 as MV00684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02727 as MV02727
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02728 as MV02728
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02729 as MV02729
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02730 as MV02730
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X12 • K1267 ≈ K1267 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X12 • K1267} {g' = K1267 • X27 • M2 • M7} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02727.proved (MV00684.proved))) (trans (cong refl Base.proved) (move-product MV00684.proved (move-product MV02728.proved (move-product MV02729.proved (MV02730.proved))))))
