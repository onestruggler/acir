{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij253467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01447 as MV01447
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01448 as MV01448
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K3467 ≈ K3467 • X25
proved = GL.•-cancelʳ {g = X25 • K3467} {g' = K3467 • X25} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01447.proved (MV01448.proved))) (trans (cong refl Base.proved) (move-product MV01448.proved (MV01447.proved))))
