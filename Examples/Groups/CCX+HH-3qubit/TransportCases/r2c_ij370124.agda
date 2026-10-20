{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01594 as MV01594
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01595 as MV01595
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K0124 ≈ K0124 • X37
proved = GL.•-cancelʳ {g = X37 • K0124} {g' = K0124 • X37} {h = p (s3 • s6 • s5)}
  (trans (sym (move-product MV01594.proved (MV01595.proved))) (trans (cong refl Base.proved) (move-product MV01595.proved (MV01594.proved))))
