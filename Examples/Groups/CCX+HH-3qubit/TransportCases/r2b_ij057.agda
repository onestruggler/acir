{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij057 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00759 as MV00759
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00760 as MV00760
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X05 • M7 ≈ M7 • X05
proved = GL.•-cancelʳ {g = X05 • M7} {g' = M7 • X05} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00759.proved (MV00760.proved))) (trans (cong refl Base.proved) (move-product MV00760.proved (MV00759.proved))))
