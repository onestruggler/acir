{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij471235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01701 as MV01701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01702 as MV01702
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K1235 ≈ K1235 • X47
proved = GL.•-cancelʳ {g = X47 • K1235} {g' = K1235 • X47} {h = p (s0 • s1 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01701.proved (MV01702.proved))) (trans (cong refl Base.proved) (move-product MV01702.proved (MV01701.proved))))
