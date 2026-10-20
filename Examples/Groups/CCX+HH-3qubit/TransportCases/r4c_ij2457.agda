{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2457 ; X47 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00702 as MV00702
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02800 as MV02800
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03024 as MV03024
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X57 • K2457 ≈ K2457 • X47
proved = GL.•-cancelʳ {g = X57 • K2457} {g' = K2457 • X47} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03024.proved (MV00702.proved))) (trans (cong refl Base.proved) (move-product MV00702.proved (MV02800.proved))))
