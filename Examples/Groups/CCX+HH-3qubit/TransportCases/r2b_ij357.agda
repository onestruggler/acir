{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00936 as MV00936
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00937 as MV00937
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X35 • M7 ≈ M7 • X35
proved = GL.•-cancelʳ {g = X35 • M7} {g' = M7 • X35} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00936.proved (MV00937.proved))) (trans (cong refl Base.proved) (move-product MV00937.proved (MV00936.proved))))
