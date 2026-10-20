{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij13470256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; K1347 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00687 as MV00687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02427 as MV02427
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1347 • K0256 ≈ K0256 • K1347
proved = GL.•-cancelʳ {g = K1347 • K0256} {g' = K0256 • K1347} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00687.proved (MV02427.proved))) (trans (cong refl Base.proved) (move-product MV02427.proved (MV00687.proved))))
