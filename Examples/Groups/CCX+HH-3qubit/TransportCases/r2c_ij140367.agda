{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01266 as MV01266
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01267 as MV01267
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0367 ≈ K0367 • X14
proved = GL.•-cancelʳ {g = X14 • K0367} {g' = K0367 • X14} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01266.proved (MV01267.proved))) (trans (cong refl Base.proved) (move-product MV01267.proved (MV01266.proved))))
