{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij32467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02101 as MV02101
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02102 as MV02102
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K2467 ≈ K2467 • M3
proved = GL.•-cancelʳ {g = M3 • K2467} {g' = K2467 • M3} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02101.proved (MV02102.proved))) (trans (cong refl Base.proved) (move-product MV02102.proved (MV02101.proved))))
