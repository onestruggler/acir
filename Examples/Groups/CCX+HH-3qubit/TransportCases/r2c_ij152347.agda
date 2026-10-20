{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij152347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2347 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01301 as MV01301
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01302 as MV01302
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K2347 ≈ K2347 • X15
proved = GL.•-cancelʳ {g = X15 • K2347} {g' = K2347 • X15} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01301.proved (MV01302.proved))) (trans (cong refl Base.proved) (move-product MV01302.proved (MV01301.proved))))
