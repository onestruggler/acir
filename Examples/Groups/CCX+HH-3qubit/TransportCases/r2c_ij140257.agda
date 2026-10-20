{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01258 as MV01258
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01259 as MV01259
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0257 ≈ K0257 • X14
proved = GL.•-cancelʳ {g = X14 • K0257} {g' = K0257 • X14} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01258.proved (MV01259.proved))) (trans (cong refl Base.proved) (move-product MV01259.proved (MV01258.proved))))
