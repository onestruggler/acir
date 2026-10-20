{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij132457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2457 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01245 as MV01245
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01246 as MV01246
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K2457 ≈ K2457 • X13
proved = GL.•-cancelʳ {g = X13 • K2457} {g' = K2457 • X13} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01245.proved (MV01246.proved))) (trans (cong refl Base.proved) (move-product MV01246.proved (MV01245.proved))))
