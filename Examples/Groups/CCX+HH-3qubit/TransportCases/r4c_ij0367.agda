{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; X37 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00670 as MV00670
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02672 as MV02672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02992 as MV02992
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K0367 ≈ K0367 • X37
proved = GL.•-cancelʳ {g = X67 • K0367} {g' = K0367 • X37} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02992.proved (MV00670.proved))) (trans (cong refl Base.proved) (move-product MV00670.proved (MV02672.proved))))
