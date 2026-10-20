{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00680 as MV00680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01070 as MV01070
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1246 ≈ K1246 • X03
proved = GL.•-cancelʳ {g = X03 • K1246} {g' = K1246 • X03} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01070.proved (MV00680.proved))) (trans (cong refl Base.proved) (move-product MV00680.proved (MV01070.proved))))
