{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij172356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01363 as MV01363
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01364 as MV01364
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X17 • K2356 ≈ K2356 • X17
proved = GL.•-cancelʳ {g = X17 • K2356} {g' = K2356 • X17} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01363.proved (MV01364.proved))) (trans (cong refl Base.proved) (move-product MV01364.proved (MV01363.proved))))
