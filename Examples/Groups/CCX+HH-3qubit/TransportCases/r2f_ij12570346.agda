{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12570346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; K1257 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00683 as MV00683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02423 as MV02423
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1257 • K0346 ≈ K0346 • K1257
proved = GL.•-cancelʳ {g = K1257 • K0346} {g' = K0346 • K1257} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00683.proved (MV02423.proved))) (trans (cong refl Base.proved) (move-product MV02423.proved (MV00683.proved))))
