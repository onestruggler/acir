{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij13460257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; K1346 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00686 as MV00686
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02426 as MV02426
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1346 • K0257 ≈ K0257 • K1346
proved = GL.•-cancelʳ {g = K1346 • K0257} {g' = K0257 • K1346} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00686.proved (MV02426.proved))) (trans (cong refl Base.proved) (move-product MV02426.proved (MV00686.proved))))
