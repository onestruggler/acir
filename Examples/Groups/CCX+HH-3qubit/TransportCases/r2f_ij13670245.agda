{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij13670245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; K1367 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00690 as MV00690
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02430 as MV02430
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1367 • K0245 ≈ K0245 • K1367
proved = GL.•-cancelʳ {g = K1367 • K0245} {g' = K0245 • K1367} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00690.proved (MV02430.proved))) (trans (cong refl Base.proved) (move-product MV02430.proved (MV00690.proved))))
