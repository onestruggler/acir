{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01341 as MV01341
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01342 as MV01342
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X17 • K0235 ≈ K0235 • X17
proved = GL.•-cancelʳ {g = X17 • K0235} {g' = K0235 • X17} {h = p (s1 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01341.proved (MV01342.proved))) (trans (cong refl Base.proved) (move-product MV01342.proved (MV01341.proved))))
