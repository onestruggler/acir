{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00862 as MV00862
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00863 as MV00863
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X23 • M6 ≈ M6 • X23
proved = GL.•-cancelʳ {g = X23 • M6} {g' = M6 • X23} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00862.proved (MV00863.proved))) (trans (cong refl Base.proved) (move-product MV00863.proved (MV00862.proved))))
