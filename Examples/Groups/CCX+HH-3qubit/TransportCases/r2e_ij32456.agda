{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij32456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2456 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02097 as MV02097
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02098 as MV02098
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K2456 ≈ K2456 • M3
proved = GL.•-cancelʳ {g = M3 • K2456} {g' = K2456 • M3} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02097.proved (MV02098.proved))) (trans (cong refl Base.proved) (move-product MV02098.proved (MV02097.proved))))
