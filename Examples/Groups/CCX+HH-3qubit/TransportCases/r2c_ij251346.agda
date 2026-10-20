{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij251346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01439 as MV01439
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01440 as MV01440
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K1346 ≈ K1346 • X25
proved = GL.•-cancelʳ {g = X25 • K1346} {g' = K1346 • X25} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01439.proved (MV01440.proved))) (trans (cong refl Base.proved) (move-product MV01440.proved (MV01439.proved))))
