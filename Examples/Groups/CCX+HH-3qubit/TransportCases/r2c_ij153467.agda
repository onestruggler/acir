{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij153467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01307 as MV01307
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01308 as MV01308
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K3467 ≈ K3467 • X15
proved = GL.•-cancelʳ {g = X15 • K3467} {g' = K3467 • X15} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01307.proved (MV01308.proved))) (trans (cong refl Base.proved) (move-product MV01308.proved (MV01307.proved))))
