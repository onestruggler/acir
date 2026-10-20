{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij25670134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; K2567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00704 as MV00704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02444 as MV02444
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2567 • K0134 ≈ K0134 • K2567
proved = GL.•-cancelʳ {g = K2567 • K0134} {g' = K0134 • K2567} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00704.proved (MV02444.proved))) (trans (cong refl Base.proved) (move-product MV02444.proved (MV00704.proved))))
