{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; M0 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00664 as MV00664
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02873 as MV02873
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02874 as MV02874
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X26 • K0267 ≈ M0 • K0267 • M0 • K0267 • M0
proved = GL.•-cancelʳ {g = X26 • K0267} {g' = M0 • K0267 • M0 • K0267 • M0} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02873.proved (MV00664.proved))) (trans (cong refl Base.proved) (move-product MV02874.proved (move-product MV00664.proved (move-product MV02874.proved (move-product MV00664.proved (MV02874.proved)))))))
