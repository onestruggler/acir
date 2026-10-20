{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij062357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01173 as MV01173
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01174 as MV01174
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K2357 ≈ K2357 • X06
proved = GL.•-cancelʳ {g = X06 • K2357} {g' = K2357 • X06} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01173.proved (MV01174.proved))) (trans (cong refl Base.proved) (move-product MV01174.proved (MV01173.proved))))
