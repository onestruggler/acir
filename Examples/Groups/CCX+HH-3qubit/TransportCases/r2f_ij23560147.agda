{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij23560147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; K2356 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00698 as MV00698
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02438 as MV02438
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2356 • K0147 ≈ K0147 • K2356
proved = GL.•-cancelʳ {g = K2356 • K0147} {g' = K0147 • K2356} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00698.proved (MV02438.proved))) (trans (cong refl Base.proved) (move-product MV02438.proved (MV00698.proved))))
