{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij265 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00898 as MV00898
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00899 as MV00899
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X26 • M5 ≈ M5 • X26
proved = GL.•-cancelʳ {g = X26 • M5} {g' = M5 • X26} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00898.proved (MV00899.proved))) (trans (cong refl Base.proved) (move-product MV00899.proved (MV00898.proved))))
