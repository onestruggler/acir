{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02571346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; K1346 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02403 as MV02403
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0257 • K1346 ≈ K1346 • K0257
proved = GL.•-cancelʳ {g = K0257 • K1346} {g' = K1346 • K0257} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00663.proved (MV02403.proved))) (trans (cong refl Base.proved) (move-product MV02403.proved (MV00663.proved))))
