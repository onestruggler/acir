{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; M0 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02889 as MV02889
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02890 as MV02890
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X45 • K0457 ≈ M0 • K0457 • M0 • K0457 • M0
proved = GL.•-cancelʳ {g = X45 • K0457} {g' = M0 • K0457 • M0 • K0457 • M0} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02889.proved (MV00672.proved))) (trans (cong refl Base.proved) (move-product MV02890.proved (move-product MV00672.proved (move-product MV02890.proved (move-product MV00672.proved (MV02890.proved)))))))
