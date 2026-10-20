{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij61457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02300 as MV02300
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02301 as MV02301
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K1457 ≈ K1457 • M6
proved = GL.•-cancelʳ {g = M6 • K1457} {g' = K1457 • M6} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02300.proved (MV02301.proved))) (trans (cong refl Base.proved) (move-product MV02301.proved (MV02300.proved))))
