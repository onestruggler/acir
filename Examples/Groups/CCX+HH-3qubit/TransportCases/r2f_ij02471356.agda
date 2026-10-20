{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02471356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; K1356 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00661 as MV00661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02401 as MV02401
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0247 • K1356 ≈ K1356 • K0247
proved = GL.•-cancelʳ {g = K0247 • K1356} {g' = K1356 • K0247} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00661.proved (MV02401.proved))) (trans (cong refl Base.proved) (move-product MV02401.proved (MV00661.proved))))
