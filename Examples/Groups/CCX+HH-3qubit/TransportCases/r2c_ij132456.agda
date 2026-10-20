{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij132456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2456 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01243 as MV01243
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01244 as MV01244
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K2456 ≈ K2456 • X13
proved = GL.•-cancelʳ {g = X13 • K2456} {g' = K2456 • X13} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01243.proved (MV01244.proved))) (trans (cong refl Base.proved) (move-product MV01244.proved (MV01243.proved))))
