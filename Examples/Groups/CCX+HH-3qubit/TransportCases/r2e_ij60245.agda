{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02268 as MV02268
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02269 as MV02269
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0245 ≈ K0245 • M6
proved = GL.•-cancelʳ {g = M6 • K0245} {g' = K0245 • M6} {h = p (s1 • s3 • s2 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02268.proved (MV02269.proved))) (trans (cong refl Base.proved) (move-product MV02269.proved (MV02268.proved))))
