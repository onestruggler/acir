{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij23670145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; K2367 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00700 as MV00700
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02440 as MV02440
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K2367 • K0145 ≈ K0145 • K2367
proved = GL.•-cancelʳ {g = K2367 • K0145} {g' = K0145 • K2367} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00700.proved (MV02440.proved))) (trans (cong refl Base.proved) (move-product MV02440.proved (MV00700.proved))))
