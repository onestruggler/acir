{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij15670234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K1567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00694 as MV00694
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02434 as MV02434
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1567 • K0234 ≈ K0234 • K1567
proved = GL.•-cancelʳ {g = K1567 • K0234} {g' = K0234 • K1567} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00694.proved (MV02434.proved))) (trans (cong refl Base.proved) (move-product MV02434.proved (MV00694.proved))))
