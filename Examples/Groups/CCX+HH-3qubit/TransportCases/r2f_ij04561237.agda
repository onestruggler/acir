{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij04561237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; K1237 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00671 as MV00671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02411 as MV02411
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0456 • K1237 ≈ K1237 • K0456
proved = GL.•-cancelʳ {g = K0456 • K1237} {g' = K1237 • K0456} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00671.proved (MV02411.proved))) (trans (cong refl Base.proved) (move-product MV02411.proved (MV00671.proved))))
