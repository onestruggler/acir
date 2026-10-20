{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij261 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00892 as MV00892
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00893 as MV00893
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X26 • M1 ≈ M1 • X26
proved = GL.•-cancelʳ {g = X26 • M1} {g' = M1 • X26} {h = p (s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00892.proved (MV00893.proved))) (trans (cong refl Base.proved) (move-product MV00893.proved (MV00892.proved))))
