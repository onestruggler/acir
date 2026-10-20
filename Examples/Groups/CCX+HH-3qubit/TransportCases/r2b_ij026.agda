{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij026 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00721 as MV00721
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00722 as MV00722
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X02 • M6 ≈ M6 • X02
proved = GL.•-cancelʳ {g = X02 • M6} {g' = M6 • X02} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2)}
  (trans (sym (move-product MV00721.proved (MV00722.proved))) (trans (cong refl Base.proved) (move-product MV00722.proved (MV00721.proved))))
