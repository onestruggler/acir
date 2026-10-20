{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01079 as MV01079
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01080 as MV01080
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1467 ≈ K1467 • X03
proved = GL.•-cancelʳ {g = X03 • K1467} {g' = K1467 • X03} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01079.proved (MV01080.proved))) (trans (cong refl Base.proved) (move-product MV01080.proved (MV01079.proved))))
