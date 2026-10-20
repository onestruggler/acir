{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01343 as MV01343
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01344 as MV01344
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X17 • K0236 ≈ K0236 • X17
proved = GL.•-cancelʳ {g = X17 • K0236} {g' = K0236 • X17} {h = p (s1 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01343.proved (MV01344.proved))) (trans (cong refl Base.proved) (move-product MV01344.proved (MV01343.proved))))
