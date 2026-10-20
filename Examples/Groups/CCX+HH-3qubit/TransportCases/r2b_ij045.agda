{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij045 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X04 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00743 as MV00743
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00744 as MV00744
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X04 • M5 ≈ M5 • X04
proved = GL.•-cancelʳ {g = X04 • M5} {g' = M5 • X04} {h = p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00743.proved (MV00744.proved))) (trans (cong refl Base.proved) (move-product MV00744.proved (MV00743.proved))))
