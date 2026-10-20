{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02137 as MV02137
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02138 as MV02138
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0356 ≈ K0356 • M4
proved = GL.•-cancelʳ {g = M4 • K0356} {g' = K0356 • M4} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02137.proved (MV02138.proved))) (trans (cong refl Base.proved) (move-product MV02138.proved (MV02137.proved))))
