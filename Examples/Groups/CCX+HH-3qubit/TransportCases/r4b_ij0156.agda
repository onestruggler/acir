{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; M0 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02850 as MV02850
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02851 as MV02851
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X15 • K0156 ≈ M0 • K0156 • M0 • K0156 • M0
proved = GL.•-cancelʳ {g = X15 • K0156} {g' = M0 • K0156 • M0 • K0156 • M0} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02850.proved (MV00652.proved))) (trans (cong refl Base.proved) (move-product MV02851.proved (move-product MV00652.proved (move-product MV02851.proved (move-product MV00652.proved (MV02851.proved)))))))
