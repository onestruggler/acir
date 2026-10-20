{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij052347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2347 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01141 as MV01141
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01142 as MV01142
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K2347 ≈ K2347 • X05
proved = GL.•-cancelʳ {g = X05 • K2347} {g' = K2347 • X05} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01141.proved (MV01142.proved))) (trans (cong refl Base.proved) (move-product MV01142.proved (MV01141.proved))))
