{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij173 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00846 as MV00846
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00847 as MV00847
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X17 • M3 ≈ M3 • X17
proved = GL.•-cancelʳ {g = X17 • M3} {g' = M3 • X17} {h = p (s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00846.proved (MV00847.proved))) (trans (cong refl Base.proved) (move-product MV00847.proved (MV00846.proved))))
