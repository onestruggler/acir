{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij142367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01274 as MV01274
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01275 as MV01275
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K2367 ≈ K2367 • X14
proved = GL.•-cancelʳ {g = X14 • K2367} {g' = K2367 • X14} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01274.proved (MV01275.proved))) (trans (cong refl Base.proved) (move-product MV01275.proved (MV01274.proved))))
