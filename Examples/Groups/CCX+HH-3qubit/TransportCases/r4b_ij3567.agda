{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij3567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; M3 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00708 as MV00708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02960 as MV02960
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02961 as MV02961
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X56 • K3567 ≈ M3 • K3567 • M3 • K3567 • M3
proved = GL.•-cancelʳ {g = X56 • K3567} {g' = M3 • K3567 • M3 • K3567 • M3} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02960.proved (MV00708.proved))) (trans (cong refl Base.proved) (move-product MV02961.proved (move-product MV00708.proved (move-product MV02961.proved (move-product MV00708.proved (MV02961.proved)))))))
