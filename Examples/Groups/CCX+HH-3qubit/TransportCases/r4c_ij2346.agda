{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2346 ; X36 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00696 as MV00696
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02776 as MV02776
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03018 as MV03018
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X46 • K2346 ≈ K2346 • X36
proved = GL.•-cancelʳ {g = X46 • K2346} {g' = K2346 • X36} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03018.proved (MV00696.proved))) (trans (cong refl Base.proved) (move-product MV00696.proved (MV02776.proved))))
