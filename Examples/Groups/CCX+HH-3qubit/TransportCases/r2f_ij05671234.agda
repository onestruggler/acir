{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij05671234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; K1234 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00674 as MV00674
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02414 as MV02414
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0567 • K1234 ≈ K1234 • K0567
proved = GL.•-cancelʳ {g = K0567 • K1234} {g' = K1234 • K0567} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00674.proved (MV02414.proved))) (trans (cong refl Base.proved) (move-product MV02414.proved (MV00674.proved))))
