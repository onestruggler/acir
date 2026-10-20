{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02199 as MV02199
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02200 as MV02200
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0246 ≈ K0246 • M5
proved = GL.•-cancelʳ {g = M5 • K0246} {g' = K0246 • M5} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02199.proved (MV02200.proved))) (trans (cong refl Base.proved) (move-product MV02200.proved (MV02199.proved))))
