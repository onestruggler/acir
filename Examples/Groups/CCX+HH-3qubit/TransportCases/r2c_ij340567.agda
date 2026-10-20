{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01524 as MV01524
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01525 as MV01525
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0567 ≈ K0567 • X34
proved = GL.•-cancelʳ {g = X34 • K0567} {g' = K0567 • X34} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01524.proved (MV01525.proved))) (trans (cong refl Base.proved) (move-product MV01525.proved (MV01524.proved))))
