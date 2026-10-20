{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00972 as MV00972
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00973 as MV00973
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X45 • M7 ≈ M7 • X45
proved = GL.•-cancelʳ {g = X45 • M7} {g' = M7 • X45} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00972.proved (MV00973.proved))) (trans (cong refl Base.proved) (move-product MV00973.proved (MV00972.proved))))
