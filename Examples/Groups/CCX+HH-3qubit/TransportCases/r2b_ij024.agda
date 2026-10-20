{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij024 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00717 as MV00717
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00718 as MV00718
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X02 • M4 ≈ M4 • X02
proved = GL.•-cancelʳ {g = X02 • M4} {g' = M4 • X02} {h = p (s3 • s2 • s1 • s0 • s2)}
  (trans (sym (move-product MV00717.proved (MV00718.proved))) (trans (cong refl Base.proved) (move-product MV00718.proved (MV00717.proved))))
