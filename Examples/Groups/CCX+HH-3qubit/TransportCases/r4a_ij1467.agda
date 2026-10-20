{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; M4 ; M7 ; X14 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00693 as MV00693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02763 as MV02763
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02764 as MV02764
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02765 as MV02765
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02766 as MV02766
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X14 • K1467 ≈ K1467 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X14 • K1467} {g' = K1467 • X47 • M4 • M7} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02763.proved (MV00693.proved))) (trans (cong refl Base.proved) (move-product MV00693.proved (move-product MV02764.proved (move-product MV02765.proved (MV02766.proved))))))
