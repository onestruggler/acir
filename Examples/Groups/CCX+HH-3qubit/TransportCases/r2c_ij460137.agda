{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01659 as MV01659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01660 as MV01660
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K0137 ≈ K0137 • X46
proved = GL.•-cancelʳ {g = X46 • K0137} {g' = K0137 • X46} {h = p (s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01659.proved (MV01660.proved))) (trans (cong refl Base.proved) (move-product MV01660.proved (MV01659.proved))))
