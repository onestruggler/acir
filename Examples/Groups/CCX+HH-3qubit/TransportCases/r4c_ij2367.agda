{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; X37 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00700 as MV00700
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02792 as MV02792
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03022 as MV03022
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K2367 ≈ K2367 • X37
proved = GL.•-cancelʳ {g = X67 • K2367} {g' = K2367 • X37} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03022.proved (MV00700.proved))) (trans (cong refl Base.proved) (move-product MV00700.proved (MV02792.proved))))
