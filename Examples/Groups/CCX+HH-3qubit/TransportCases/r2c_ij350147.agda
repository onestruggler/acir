{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01542 as MV01542
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01543 as MV01543
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0147 ≈ K0147 • X35
proved = GL.•-cancelʳ {g = X35 • K0147} {g' = K0147 • X35} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01542.proved (MV01543.proved))) (trans (cong refl Base.proved) (move-product MV01543.proved (MV01542.proved))))
