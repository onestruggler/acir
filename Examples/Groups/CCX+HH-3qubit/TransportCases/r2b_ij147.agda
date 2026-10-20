{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00816 as MV00816
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00817 as MV00817
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X14 • M7 ≈ M7 • X14
proved = GL.•-cancelʳ {g = X14 • M7} {g' = M7 • X14} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00816.proved (MV00817.proved))) (trans (cong refl Base.proved) (move-product MV00817.proved (MV00816.proved))))
