{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij460357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01669 as MV01669
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01670 as MV01670
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K0357 ≈ K0357 • X46
proved = GL.•-cancelʳ {g = X46 • K0357} {g' = K0357 • X46} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01669.proved (MV01670.proved))) (trans (cong refl Base.proved) (move-product MV01670.proved (MV01669.proved))))
