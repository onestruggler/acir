{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij561237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01733 as MV01733
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01734 as MV01734
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K1237 ≈ K1237 • X56
proved = GL.•-cancelʳ {g = X56 • K1237} {g' = K1237 • X56} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01733.proved (MV01734.proved))) (trans (cong refl Base.proved) (move-product MV01734.proved (MV01733.proved))))
