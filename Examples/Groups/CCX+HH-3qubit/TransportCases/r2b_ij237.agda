{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00864 as MV00864
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00865 as MV00865
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X23 • M7 ≈ M7 • X23
proved = GL.•-cancelʳ {g = X23 • M7} {g' = M7 • X23} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)}
  (trans (sym (move-product MV00864.proved (MV00865.proved))) (trans (cong refl Base.proved) (move-product MV00865.proved (MV00864.proved))))
