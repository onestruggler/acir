{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01600 as MV01600
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01601 as MV01601
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K0145 ≈ K0145 • X37
proved = GL.•-cancelʳ {g = X37 • K0145} {g' = K0145 • X37} {h = p (s3 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01600.proved (MV01601.proved))) (trans (cong refl Base.proved) (move-product MV01601.proved (MV01600.proved))))
