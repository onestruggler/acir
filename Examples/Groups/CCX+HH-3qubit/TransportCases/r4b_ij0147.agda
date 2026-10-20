{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; M0 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02848 as MV02848
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02849 as MV02849
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X14 • K0147 ≈ M0 • K0147 • M0 • K0147 • M0
proved = GL.•-cancelʳ {g = X14 • K0147} {g' = M0 • K0147 • M0 • K0147 • M0} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02848.proved (MV00651.proved))) (trans (cong refl Base.proved) (move-product MV02849.proved (move-product MV00651.proved (move-product MV02849.proved (move-product MV00651.proved (MV02849.proved)))))))
