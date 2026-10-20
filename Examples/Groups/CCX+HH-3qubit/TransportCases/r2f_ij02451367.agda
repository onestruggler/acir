{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02451367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; K1367 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00659 as MV00659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02399 as MV02399
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0245 • K1367 ≈ K1367 • K0245
proved = GL.•-cancelʳ {g = K0245 • K1367} {g' = K1367 • K0245} {h = p (s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00659.proved (MV02399.proved))) (trans (cong refl Base.proved) (move-product MV02399.proved (MV00659.proved))))
