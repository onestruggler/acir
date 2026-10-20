{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij71356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02367 as MV02367
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02368 as MV02368
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K1356 ≈ K1356 • M7
proved = GL.•-cancelʳ {g = M7 • K1356} {g' = K1356 • M7} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02367.proved (MV02368.proved))) (trans (cong refl Base.proved) (move-product MV02368.proved (MV02367.proved))))
