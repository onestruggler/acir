{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01665 as MV01665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01666 as MV01666
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K0237 ≈ K0237 • X46
proved = GL.•-cancelʳ {g = X46 • K0237} {g' = K0237 • X46} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01665.proved (MV01666.proved))) (trans (cong refl Base.proved) (move-product MV01666.proved (MV01665.proved))))
