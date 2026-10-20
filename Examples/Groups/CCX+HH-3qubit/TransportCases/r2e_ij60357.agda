{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02278 as MV02278
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02279 as MV02279
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0357 ≈ K0357 • M6
proved = GL.•-cancelʳ {g = M6 • K0357} {g' = K0357 • M6} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02278.proved (MV02279.proved))) (trans (cong refl Base.proved) (move-product MV02279.proved (MV02278.proved))))
