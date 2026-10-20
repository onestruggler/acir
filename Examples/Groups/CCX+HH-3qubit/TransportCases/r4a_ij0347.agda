{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; M3 ; M7 ; X03 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00667 as MV00667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02659 as MV02659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02660 as MV02660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02661 as MV02661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02662 as MV02662
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X03 • K0347 ≈ K0347 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X03 • K0347} {g' = K0347 • X37 • M3 • M7} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02659.proved (MV00667.proved))) (trans (cong refl Base.proved) (move-product MV00667.proved (move-product MV02660.proved (move-product MV02661.proved (MV02662.proved))))))
