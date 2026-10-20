{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij341267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01530 as MV01530
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01531 as MV01531
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K1267 ≈ K1267 • X34
proved = GL.•-cancelʳ {g = X34 • K1267} {g' = K1267 • X34} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01530.proved (MV01531.proved))) (trans (cong refl Base.proved) (move-product MV01531.proved (MV01530.proved))))
