{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01137 as MV01137
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01138 as MV01138
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K1467 ≈ K1467 • X05
proved = GL.•-cancelʳ {g = X05 • K1467} {g' = K1467 • X05} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01137.proved (MV01138.proved))) (trans (cong refl Base.proved) (move-product MV01138.proved (MV01137.proved))))
