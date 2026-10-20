{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij14570236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; K1457 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00692 as MV00692
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02432 as MV02432
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1457 • K0236 ≈ K0236 • K1457
proved = GL.•-cancelʳ {g = K1457 • K0236} {g' = K0236 • K1457} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00692.proved (MV02432.proved))) (trans (cong refl Base.proved) (move-product MV02432.proved (MV00692.proved))))
