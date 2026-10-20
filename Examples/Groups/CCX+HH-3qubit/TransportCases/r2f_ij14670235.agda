{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij14670235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; K1467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00693 as MV00693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02433 as MV02433
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1467 • K0235 ≈ K0235 • K1467
proved = GL.•-cancelʳ {g = K1467 • K0235} {g' = K0235 • K1467} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00693.proved (MV02433.proved))) (trans (cong refl Base.proved) (move-product MV02433.proved (MV00693.proved))))
