{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij021346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00686 as MV00686
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01050 as MV01050
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X02 • K1346 ≈ K1346 • X02
proved = GL.•-cancelʳ {g = X02 • K1346} {g' = K1346 • X02} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01050.proved (MV00686.proved))) (trans (cong refl Base.proved) (move-product MV00686.proved (MV01050.proved))))
