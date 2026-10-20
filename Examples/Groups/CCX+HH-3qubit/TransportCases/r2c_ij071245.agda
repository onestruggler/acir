{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01185 as MV01185
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01186 as MV01186
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X07 • K1245 ≈ K1245 • X07
proved = GL.•-cancelʳ {g = X07 • K1245} {g' = K1245 • X07} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01185.proved (MV01186.proved))) (trans (cong refl Base.proved) (move-product MV01186.proved (MV01185.proved))))
