{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02193 as MV02193
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02194 as MV02194
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0234 ≈ K0234 • M5
proved = GL.•-cancelʳ {g = M5 • K0234} {g' = K0234 • M5} {h = p (s1 • s2 • s3 • s4)}
  (trans (sym (move-product MV02193.proved (MV02194.proved))) (trans (cong refl Base.proved) (move-product MV02194.proved (MV02193.proved))))
