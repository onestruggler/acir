{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00984 as MV00984
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00985 as MV00985
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X46 • M7 ≈ M7 • X46
proved = GL.•-cancelʳ {g = X46 • M7} {g' = M7 • X46} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00984.proved (MV00985.proved))) (trans (cong refl Base.proved) (move-product MV00985.proved (MV00984.proved))))
