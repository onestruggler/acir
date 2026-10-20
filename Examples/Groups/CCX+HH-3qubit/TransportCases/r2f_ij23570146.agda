{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij23570146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; K2357 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00699 as MV00699
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02439 as MV02439
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2357 • K0146 ≈ K0146 • K2357
proved = GL.•-cancelʳ {g = K2357 • K0146} {g' = K0146 • K2357} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00699.proved (MV02439.proved))) (trans (cong refl Base.proved) (move-product MV02439.proved (MV00699.proved))))
