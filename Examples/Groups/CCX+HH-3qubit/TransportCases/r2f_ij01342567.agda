{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01342567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; K2567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02385 as MV02385
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0134 • K2567 ≈ K2567 • K0134
proved = GL.•-cancelʳ {g = K0134 • K2567} {g' = K2567 • K0134} {h = p (s2 • s3)}
  (trans (sym (move-product MV00645.proved (MV02385.proved))) (trans (cong refl Base.proved) (move-product MV02385.proved (MV00645.proved))))
