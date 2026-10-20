{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij052467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01145 as MV01145
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01146 as MV01146
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K2467 ≈ K2467 • X05
proved = GL.•-cancelʳ {g = X05 • K2467} {g' = K2467 • X05} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01145.proved (MV01146.proved))) (trans (cong refl Base.proved) (move-product MV01146.proved (MV01145.proved))))
