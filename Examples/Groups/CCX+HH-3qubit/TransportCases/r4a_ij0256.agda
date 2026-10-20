{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; M2 ; M6 ; X02 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02639 as MV02639
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02640 as MV02640
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02641 as MV02641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02642 as MV02642
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X02 • K0256 ≈ K0256 • X26 • M2 • M6
proved = GL.•-cancelʳ {g = X02 • K0256} {g' = K0256 • X26 • M2 • M6} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02639.proved (MV00662.proved))) (trans (cong refl Base.proved) (move-product MV00662.proved (move-product MV02640.proved (move-product MV02641.proved (MV02642.proved))))))
