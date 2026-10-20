{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij176 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00852 as MV00852
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00853 as MV00853
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X17 • M6 ≈ M6 • X17
proved = GL.•-cancelʳ {g = X17 • M6} {g' = M6 • X17} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00852.proved (MV00853.proved))) (trans (cong refl Base.proved) (move-product MV00853.proved (MV00852.proved))))
