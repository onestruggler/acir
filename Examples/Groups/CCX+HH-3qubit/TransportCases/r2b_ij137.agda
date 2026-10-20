{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00804 as MV00804
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00805 as MV00805
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X13 • M7 ≈ M7 • X13
proved = GL.•-cancelʳ {g = X13 • M7} {g' = M7 • X13} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00804.proved (MV00805.proved))) (trans (cong refl Base.proved) (move-product MV00805.proved (MV00804.proved))))
