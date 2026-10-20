{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; M2 ; M7 ; X02 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02643 as MV02643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02644 as MV02644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02645 as MV02645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02646 as MV02646
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X02 • K0257 ≈ K0257 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X02 • K0257} {g' = K0257 • X27 • M2 • M7} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02643.proved (MV00663.proved))) (trans (cong refl Base.proved) (move-product MV00663.proved (move-product MV02644.proved (move-product MV02645.proved (MV02646.proved))))))
