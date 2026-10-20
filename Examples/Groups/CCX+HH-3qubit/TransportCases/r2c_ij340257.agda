{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01520 as MV01520
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01521 as MV01521
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0257 ≈ K0257 • X34
proved = GL.•-cancelʳ {g = X34 • K0257} {g' = K0257 • X34} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01520.proved (MV01521.proved))) (trans (cong refl Base.proved) (move-product MV01521.proved (MV01520.proved))))
