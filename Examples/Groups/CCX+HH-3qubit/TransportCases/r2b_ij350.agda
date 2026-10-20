{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij350 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00926 as MV00926
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00927 as MV00927
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X35 • M0 ≈ M0 • X35
proved = GL.•-cancelʳ {g = X35 • M0} {g' = M0 • X35} {h = p (s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00926.proved (MV00927.proved))) (trans (cong refl Base.proved) (move-product MV00927.proved (MV00926.proved))))
