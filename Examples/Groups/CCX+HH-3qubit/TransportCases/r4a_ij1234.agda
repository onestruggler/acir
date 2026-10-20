{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; M2 ; M4 ; X12 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00675 as MV00675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02691 as MV02691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02692 as MV02692
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02693 as MV02693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02694 as MV02694
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X12 • K1234 ≈ K1234 • X24 • M2 • M4
proved = GL.•-cancelʳ {g = X12 • K1234} {g' = K1234 • X24 • M2 • M4} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV02691.proved (MV00675.proved))) (trans (cong refl Base.proved) (move-product MV00675.proved (move-product MV02692.proved (move-product MV02693.proved (MV02694.proved))))))
