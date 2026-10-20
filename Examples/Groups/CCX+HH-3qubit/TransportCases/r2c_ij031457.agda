{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01077 as MV01077
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01078 as MV01078
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1457 ≈ K1457 • X03
proved = GL.•-cancelʳ {g = X03 • K1457} {g' = K1457 • X03} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01077.proved (MV01078.proved))) (trans (cong refl Base.proved) (move-product MV01078.proved (MV01077.proved))))
