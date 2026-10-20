{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij23450167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; K2345 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00695 as MV00695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02435 as MV02435
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2345 • K0167 ≈ K0167 • K2345
proved = GL.•-cancelʳ {g = K2345 • K0167} {g' = K0167 • K2345} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00695.proved (MV02435.proved))) (trans (cong refl Base.proved) (move-product MV02435.proved (MV00695.proved))))
