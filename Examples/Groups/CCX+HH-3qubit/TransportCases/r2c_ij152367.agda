{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij152367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01303 as MV01303
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01304 as MV01304
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K2367 ≈ K2367 • X15
proved = GL.•-cancelʳ {g = X15 • K2367} {g' = K2367 • X15} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01303.proved (MV01304.proved))) (trans (cong refl Base.proved) (move-product MV01304.proved (MV01303.proved))))
