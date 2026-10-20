{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01544 as MV01544
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01545 as MV01545
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0167 ≈ K0167 • X35
proved = GL.•-cancelʳ {g = X35 • K0167} {g' = K0167 • X35} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01544.proved (MV01545.proved))) (trans (cong refl Base.proved) (move-product MV01545.proved (MV01544.proved))))
