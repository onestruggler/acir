{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01181 as MV01181
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01182 as MV01182
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X07 • K1235 ≈ K1235 • X07
proved = GL.•-cancelʳ {g = X07 • K1235} {g' = K1235 • X07} {h = p (s0 • s1 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01181.proved (MV01182.proved))) (trans (cong refl Base.proved) (move-product MV01182.proved (MV01181.proved))))
