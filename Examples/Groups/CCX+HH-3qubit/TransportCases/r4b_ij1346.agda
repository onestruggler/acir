{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; M1 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00686 as MV00686
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02916 as MV02916
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02917 as MV02917
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X34 • K1346 ≈ M1 • K1346 • M1 • K1346 • M1
proved = GL.•-cancelʳ {g = X34 • K1346} {g' = M1 • K1346 • M1 • K1346 • M1} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02916.proved (MV00686.proved))) (trans (cong refl Base.proved) (move-product MV02917.proved (move-product MV00686.proved (move-product MV02917.proved (move-product MV00686.proved (MV02917.proved)))))))
