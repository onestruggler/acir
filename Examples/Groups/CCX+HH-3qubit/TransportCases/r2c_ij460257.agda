{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01667 as MV01667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01668 as MV01668
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K0257 ≈ K0257 • X46
proved = GL.•-cancelʳ {g = X46 • K0257} {g' = K0257 • X46} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01667.proved (MV01668.proved))) (trans (cong refl Base.proved) (move-product MV01668.proved (MV01667.proved))))
