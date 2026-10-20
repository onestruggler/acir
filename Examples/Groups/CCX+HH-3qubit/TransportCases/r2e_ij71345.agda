{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij71345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02363 as MV02363
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02364 as MV02364
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K1345 ≈ K1345 • M7
proved = GL.•-cancelʳ {g = M7 • K1345} {g' = K1345 • M7} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02363.proved (MV02364.proved))) (trans (cong refl Base.proved) (move-product MV02364.proved (MV02363.proved))))
