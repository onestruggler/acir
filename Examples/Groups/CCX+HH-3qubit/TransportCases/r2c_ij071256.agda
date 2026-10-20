{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01189 as MV01189
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01190 as MV01190
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X07 • K1256 ≈ K1256 • X07
proved = GL.•-cancelʳ {g = X07 • K1256} {g' = K1256 • X07} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01189.proved (MV01190.proved))) (trans (cong refl Base.proved) (move-product MV01190.proved (MV01189.proved))))
