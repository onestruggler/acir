{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; M2 ; M6 ; X02 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00660 as MV00660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02631 as MV02631
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02632 as MV02632
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02633 as MV02633
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02634 as MV02634
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X02 • K0246 ≈ K0246 • X26 • M2 • M6
proved = GL.•-cancelʳ {g = X02 • K0246} {g' = K0246 • X26 • M2 • M6} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02631.proved (MV00660.proved))) (trans (cong refl Base.proved) (move-product MV00660.proved (move-product MV02632.proved (move-product MV02633.proved (MV02634.proved))))))
