{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij351467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01560 as MV01560
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01561 as MV01561
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K1467 ≈ K1467 • X35
proved = GL.•-cancelʳ {g = X35 • K1467} {g' = K1467 • X35} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01560.proved (MV01561.proved))) (trans (cong refl Base.proved) (move-product MV01561.proved (MV01560.proved))))
