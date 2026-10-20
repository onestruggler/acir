{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij371245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01614 as MV01614
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01615 as MV01615
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K1245 ≈ K1245 • X37
proved = GL.•-cancelʳ {g = X37 • K1245} {g' = K1245 • X37} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01614.proved (MV01615.proved))) (trans (cong refl Base.proved) (move-product MV01615.proved (MV01614.proved))))
