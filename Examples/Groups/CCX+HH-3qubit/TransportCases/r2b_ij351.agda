{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij351 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00928 as MV00928
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00929 as MV00929
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X35 • M1 ≈ M1 • X35
proved = GL.•-cancelʳ {g = X35 • M1} {g' = M1 • X35} {h = p (s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00928.proved (MV00929.proved))) (trans (cong refl Base.proved) (move-product MV00929.proved (MV00928.proved))))
