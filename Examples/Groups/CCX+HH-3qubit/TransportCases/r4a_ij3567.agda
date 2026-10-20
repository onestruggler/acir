{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij3567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; M5 ; M7 ; X35 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00708 as MV00708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02823 as MV02823
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02824 as MV02824
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02825 as MV02825
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02826 as MV02826
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X35 • K3567 ≈ K3567 • X57 • M5 • M7
proved = GL.•-cancelʳ {g = X35 • K3567} {g' = K3567 • X57 • M5 • M7} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02823.proved (MV00708.proved))) (trans (cong refl Base.proved) (move-product MV00708.proved (move-product MV02824.proved (move-product MV02825.proved (MV02826.proved))))))
