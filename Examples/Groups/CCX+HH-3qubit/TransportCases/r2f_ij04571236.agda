{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij04571236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; K1236 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02412 as MV02412
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0457 • K1236 ≈ K1236 • K0457
proved = GL.•-cancelʳ {g = K0457 • K1236} {g' = K1236 • K0457} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00672.proved (MV02412.proved))) (trans (cong refl Base.proved) (move-product MV02412.proved (MV00672.proved))))
