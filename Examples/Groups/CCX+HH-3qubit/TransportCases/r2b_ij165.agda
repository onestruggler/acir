{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij165 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00838 as MV00838
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00839 as MV00839
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X16 • M5 ≈ M5 • X16
proved = GL.•-cancelʳ {g = X16 • M5} {g' = M5 • X16} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00838.proved (MV00839.proved))) (trans (cong refl Base.proved) (move-product MV00839.proved (MV00838.proved))))
