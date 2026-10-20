{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij3457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3457 ; M4 ; M7 ; X34 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00706 as MV00706
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02815 as MV02815
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02816 as MV02816
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02817 as MV02817
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02818 as MV02818
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X34 • K3457 ≈ K3457 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X34 • K3457} {g' = K3457 • X47 • M4 • M7} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02815.proved (MV00706.proved))) (trans (cong refl Base.proved) (move-product MV00706.proved (move-product MV02816.proved (move-product MV02817.proved (MV02818.proved))))))
