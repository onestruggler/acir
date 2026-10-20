{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01253 as MV01253
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0235 ≈ K0235 • X14
proved = GL.•-cancelʳ {g = X14 • K0235} {g' = K0235 • X14} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV01253.proved (MV00656.proved))) (trans (cong refl Base.proved) (move-product MV00656.proved (MV01253.proved))))
