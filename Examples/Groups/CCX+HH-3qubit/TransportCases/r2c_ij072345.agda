{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij072345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01199 as MV01199
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01200 as MV01200
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X07 • K2345 ≈ K2345 • X07
proved = GL.•-cancelʳ {g = X07 • K2345} {g' = K2345 • X07} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01199.proved (MV01200.proved))) (trans (cong refl Base.proved) (move-product MV01200.proved (MV01199.proved))))
