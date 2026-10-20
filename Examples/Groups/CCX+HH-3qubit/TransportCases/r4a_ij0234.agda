{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; M2 ; M4 ; X02 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02611 as MV02611
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02612 as MV02612
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02613 as MV02613
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02614 as MV02614
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X02 • K0234 ≈ K0234 • X24 • M2 • M4
proved = GL.•-cancelʳ {g = X02 • K0234} {g' = K0234 • X24 • M2 • M4} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV02611.proved (MV00655.proved))) (trans (cong refl Base.proved) (move-product MV00655.proved (move-product MV02612.proved (move-product MV02613.proved (MV02614.proved))))))
