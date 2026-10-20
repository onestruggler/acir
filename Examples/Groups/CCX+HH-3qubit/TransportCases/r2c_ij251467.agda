{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij251467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01445 as MV01445
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01446 as MV01446
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K1467 ≈ K1467 • X25
proved = GL.•-cancelʳ {g = X25 • K1467} {g' = K1467 • X25} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01445.proved (MV01446.proved))) (trans (cong refl Base.proved) (move-product MV01446.proved (MV01445.proved))))
