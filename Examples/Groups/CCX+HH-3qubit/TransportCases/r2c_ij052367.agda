{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij052367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01143 as MV01143
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01144 as MV01144
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K2367 ≈ K2367 • X05
proved = GL.•-cancelʳ {g = X05 • K2367} {g' = K2367 • X05} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01143.proved (MV01144.proved))) (trans (cong refl Base.proved) (move-product MV01144.proved (MV01143.proved))))
