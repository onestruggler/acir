{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij561234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01731 as MV01731
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01732 as MV01732
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K1234 ≈ K1234 • X56
proved = GL.•-cancelʳ {g = X56 • K1234} {g' = K1234 • X56} {h = p (s0 • s1 • s2 • s3 • s4 • s5)}
  (trans (sym (move-product MV01731.proved (MV01732.proved))) (trans (cong refl Base.proved) (move-product MV01732.proved (MV01731.proved))))
