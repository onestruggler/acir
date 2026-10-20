{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij036 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00733 as MV00733
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00734 as MV00734
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X03 • M6 ≈ M6 • X03
proved = GL.•-cancelʳ {g = X03 • M6} {g' = M6 • X03} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2)}
  (trans (sym (move-product MV00733.proved (MV00734.proved))) (trans (cong refl Base.proved) (move-product MV00734.proved (MV00733.proved))))
