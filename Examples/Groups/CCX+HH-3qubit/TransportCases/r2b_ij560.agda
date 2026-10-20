{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij560 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00998 as MV00998
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00999 as MV00999
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X56 • M0 ≈ M0 • X56
proved = GL.•-cancelʳ {g = X56 • M0} {g' = M0 • X56} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00998.proved (MV00999.proved))) (trans (cong refl Base.proved) (move-product MV00999.proved (MV00998.proved))))
