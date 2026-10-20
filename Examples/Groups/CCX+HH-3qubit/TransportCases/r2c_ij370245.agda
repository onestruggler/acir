{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01606 as MV01606
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01607 as MV01607
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K0245 ≈ K0245 • X37
proved = GL.•-cancelʳ {g = X37 • K0245} {g' = K0245 • X37} {h = p (s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01606.proved (MV01607.proved))) (trans (cong refl Base.proved) (move-product MV01607.proved (MV01606.proved))))
