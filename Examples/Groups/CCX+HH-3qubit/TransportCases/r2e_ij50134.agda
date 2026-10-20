{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02181 as MV02181
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02182 as MV02182
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0134 ≈ K0134 • M5
proved = GL.•-cancelʳ {g = M5 • K0134} {g' = K0134 • M5} {h = p (s2 • s3 • s4)}
  (trans (sym (move-product MV02181.proved (MV02182.proved))) (trans (cong refl Base.proved) (move-product MV02182.proved (MV02181.proved))))
