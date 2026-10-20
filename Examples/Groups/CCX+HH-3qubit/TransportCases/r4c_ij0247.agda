{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; X27 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00661 as MV00661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02636 as MV02636
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02983 as MV02983
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X47 • K0247 ≈ K0247 • X27
proved = GL.•-cancelʳ {g = X47 • K0247} {g' = K0247 • X27} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02983.proved (MV00661.proved))) (trans (cong refl Base.proved) (move-product MV00661.proved (MV02636.proved))))
