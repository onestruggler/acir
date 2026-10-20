{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01345 as MV01345
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01346 as MV01346
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X17 • K0245 ≈ K0245 • X17
proved = GL.•-cancelʳ {g = X17 • K0245} {g' = K0245 • X17} {h = p (s1 • s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01345.proved (MV01346.proved))) (trans (cong refl Base.proved) (move-product MV01346.proved (MV01345.proved))))
