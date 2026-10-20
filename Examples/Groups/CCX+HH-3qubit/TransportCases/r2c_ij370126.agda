{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01598 as MV01598
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01599 as MV01599
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K0126 ≈ K0126 • X37
proved = GL.•-cancelʳ {g = X37 • K0126} {g' = K0126 • X37} {h = p (s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01598.proved (MV01599.proved))) (trans (cong refl Base.proved) (move-product MV01599.proved (MV01598.proved))))
