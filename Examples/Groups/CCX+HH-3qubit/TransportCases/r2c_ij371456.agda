{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij371456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01620 as MV01620
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01621 as MV01621
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K1456 ≈ K1456 • X37
proved = GL.•-cancelʳ {g = X37 • K1456} {g' = K1456 • X37} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01620.proved (MV01621.proved))) (trans (cong refl Base.proved) (move-product MV01621.proved (MV01620.proved))))
