{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02361457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; K1457 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00657 as MV00657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02397 as MV02397
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0236 • K1457 ≈ K1457 • K0236
proved = GL.•-cancelʳ {g = K0236 • K1457} {g' = K1457 • K0236} {h = p (s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00657.proved (MV02397.proved))) (trans (cong refl Base.proved) (move-product MV02397.proved (MV00657.proved))))
