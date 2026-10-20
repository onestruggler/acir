{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij461235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01671 as MV01671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01672 as MV01672
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K1235 ≈ K1235 • X46
proved = GL.•-cancelʳ {g = X46 • K1235} {g' = K1235 • X46} {h = p (s0 • s1 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01671.proved (MV01672.proved))) (trans (cong refl Base.proved) (move-product MV01672.proved (MV01671.proved))))
