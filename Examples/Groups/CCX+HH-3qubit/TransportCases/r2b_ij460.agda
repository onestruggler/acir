{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij460 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00974 as MV00974
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00975 as MV00975
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X46 • M0 ≈ M0 • X46
proved = GL.•-cancelʳ {g = X46 • M0} {g' = M0 • X46} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00974.proved (MV00975.proved))) (trans (cong refl Base.proved) (move-product MV00975.proved (MV00974.proved))))
