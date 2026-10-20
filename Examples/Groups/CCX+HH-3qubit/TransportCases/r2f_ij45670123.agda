{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij45670123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K4567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00632 as MV00632
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02449 as MV02449
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K4567 • K0123 ≈ K0123 • K4567
proved = GL.•-cancelʳ {g = K4567 • K0123} {g' = K0123 • K4567} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00632.proved (MV02449.proved))) (trans (cong refl Base.proved) (move-product MV02449.proved (MV00632.proved))))
