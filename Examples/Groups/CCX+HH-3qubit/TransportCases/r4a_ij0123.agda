{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; M1 ; M3 ; X01 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02555 as MV02555
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02556 as MV02556
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02557 as MV02557
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02558 as MV02558
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0123 ≈ K0123 • X13 • M1 • M3
proved = GL.•-cancelʳ {g = X01 • K0123} {g' = K0123 • X13 • M1 • M3} {h = p (ε)}
  (trans (sym (move-product MV02555.proved (MV00641.proved))) (trans (cong refl Base.proved) (move-product MV00641.proved (move-product MV02556.proved (move-product MV02557.proved (MV02558.proved))))))
