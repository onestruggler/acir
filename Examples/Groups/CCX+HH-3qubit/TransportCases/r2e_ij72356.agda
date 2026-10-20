{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij72356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02375 as MV02375
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02376 as MV02376
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K2356 ≈ K2356 • M7
proved = GL.•-cancelʳ {g = M7 • K2356} {g' = K2356 • M7} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02375.proved (MV02376.proved))) (trans (cong refl Base.proved) (move-product MV02376.proved (MV02375.proved))))
