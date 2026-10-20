{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2457 ; M4 ; M7 ; X24 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00702 as MV00702
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02799 as MV02799
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02800 as MV02800
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02801 as MV02801
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02802 as MV02802
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X24 • K2457 ≈ K2457 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X24 • K2457} {g' = K2457 • X47 • M4 • M7} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02799.proved (MV00702.proved))) (trans (cong refl Base.proved) (move-product MV00702.proved (move-product MV02800.proved (move-product MV02801.proved (MV02802.proved))))))
