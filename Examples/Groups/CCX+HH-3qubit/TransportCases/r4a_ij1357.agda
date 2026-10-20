{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1357 ; M3 ; M7 ; X13 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00689 as MV00689
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02747 as MV02747
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02748 as MV02748
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02749 as MV02749
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02750 as MV02750
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X13 • K1357 ≈ K1357 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X13 • K1357} {g' = K1357 • X37 • M3 • M7} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02747.proved (MV00689.proved))) (trans (cong refl Base.proved) (move-product MV00689.proved (move-product MV02748.proved (move-product MV02749.proved (MV02750.proved))))))
