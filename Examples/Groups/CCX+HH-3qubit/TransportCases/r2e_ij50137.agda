{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02185 as MV02185
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02186 as MV02186
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0137 ≈ K0137 • M5
proved = GL.•-cancelʳ {g = M5 • K0137} {g' = K0137 • M5} {h = p (s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02185.proved (MV02186.proved))) (trans (cong refl Base.proved) (move-product MV02186.proved (MV02185.proved))))
