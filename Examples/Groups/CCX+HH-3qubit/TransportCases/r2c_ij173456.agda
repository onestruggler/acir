{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij173456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01367 as MV01367
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01368 as MV01368
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X17 • K3456 ≈ K3456 • X17
proved = GL.•-cancelʳ {g = X17 • K3456} {g' = K3456 • X17} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01367.proved (MV01368.proved))) (trans (cong refl Base.proved) (move-product MV01368.proved (MV01367.proved))))
