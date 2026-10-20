{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij67 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01885 as MV01885
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01886 as MV01886
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M6 • M7 ≈ M7 • M6
proved = GL.•-cancelʳ {g = M6 • M7} {g' = M7 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01885.proved (MV01886.proved))) (trans (cong refl Base.proved) (move-product MV01886.proved (MV01885.proved))))
