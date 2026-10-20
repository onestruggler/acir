{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01693 as MV01693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01694 as MV01694
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0235 ≈ K0235 • X47
proved = GL.•-cancelʳ {g = X47 • K0235} {g' = K0235 • X47} {h = p (s1 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01693.proved (MV01694.proved))) (trans (cong refl Base.proved) (move-product MV01694.proved (MV01693.proved))))
