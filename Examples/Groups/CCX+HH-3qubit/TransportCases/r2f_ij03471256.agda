{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij03471256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; K1256 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00667 as MV00667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02407 as MV02407
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0347 • K1256 ≈ K1256 • K0347
proved = GL.•-cancelʳ {g = K0347 • K1256} {g' = K1256 • K0347} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00667.proved (MV02407.proved))) (trans (cong refl Base.proved) (move-product MV02407.proved (MV00667.proved))))
