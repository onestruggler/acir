{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij371246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01616 as MV01616
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01617 as MV01617
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K1246 ≈ K1246 • X37
proved = GL.•-cancelʳ {g = X37 • K1246} {g' = K1246 • X37} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01616.proved (MV01617.proved))) (trans (cong refl Base.proved) (move-product MV01617.proved (MV01616.proved))))
