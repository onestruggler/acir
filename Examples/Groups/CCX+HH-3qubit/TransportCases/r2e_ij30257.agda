{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02065 as MV02065
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02066 as MV02066
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0257 ≈ K0257 • M3
proved = GL.•-cancelʳ {g = M3 • K0257} {g' = K0257 • M3} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02065.proved (MV02066.proved))) (trans (cong refl Base.proved) (move-product MV02066.proved (MV02065.proved))))
