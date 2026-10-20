{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij251347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01441 as MV01441
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01442 as MV01442
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K1347 ≈ K1347 • X25
proved = GL.•-cancelʳ {g = X25 • K1347} {g' = K1347 • X25} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01441.proved (MV01442.proved))) (trans (cong refl Base.proved) (move-product MV01442.proved (MV01441.proved))))
