{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; M5 ; M7 ; X15 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00694 as MV00694
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02767 as MV02767
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02768 as MV02768
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02769 as MV02769
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02770 as MV02770
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X15 • K1567 ≈ K1567 • X57 • M5 • M7
proved = GL.•-cancelʳ {g = X15 • K1567} {g' = K1567 • X57 • M5 • M7} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02767.proved (MV00694.proved))) (trans (cong refl Base.proved) (move-product MV00694.proved (move-product MV02768.proved (move-product MV02769.proved (MV02770.proved))))))
