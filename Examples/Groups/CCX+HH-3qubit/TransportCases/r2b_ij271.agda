{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij271 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00904 as MV00904
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00905 as MV00905
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X27 • M1 ≈ M1 • X27
proved = GL.•-cancelʳ {g = X27 • M1} {g' = M1 • X27} {h = p (s0 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00904.proved (MV00905.proved))) (trans (cong refl Base.proved) (move-product MV00905.proved (MV00904.proved))))
