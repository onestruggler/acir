{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij042567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2567 ; X04 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01116 as MV01116
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01117 as MV01117
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X04 • K2567 ≈ K2567 • X04
proved = GL.•-cancelʳ {g = X04 • K2567} {g' = K2567 • X04} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01116.proved (MV01117.proved))) (trans (cong refl Base.proved) (move-product MV01117.proved (MV01116.proved))))
