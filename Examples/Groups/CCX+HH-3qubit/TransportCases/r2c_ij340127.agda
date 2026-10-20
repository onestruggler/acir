{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00644 as MV00644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01511 as MV01511
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0127 ≈ K0127 • X34
proved = GL.•-cancelʳ {g = X34 • K0127} {g' = K0127 • X34} {h = p (s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01511.proved (MV00644.proved))) (trans (cong refl Base.proved) (move-product MV00644.proved (MV01511.proved))))
