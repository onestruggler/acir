{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij034 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00729 as MV00729
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00730 as MV00730
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X03 • M4 ≈ M4 • X03
proved = GL.•-cancelʳ {g = X03 • M4} {g' = M4 • X03} {h = p (s3 • s2 • s1 • s0 • s3 • s2)}
  (trans (sym (move-product MV00729.proved (MV00730.proved))) (trans (cong refl Base.proved) (move-product MV00730.proved (MV00729.proved))))
