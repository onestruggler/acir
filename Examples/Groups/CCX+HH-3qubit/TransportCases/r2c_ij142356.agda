{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij142356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01270 as MV01270
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01271 as MV01271
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K2356 ≈ K2356 • X14
proved = GL.•-cancelʳ {g = X14 • K2356} {g' = K2356 • X14} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01270.proved (MV01271.proved))) (trans (cong refl Base.proved) (move-product MV01271.proved (MV01270.proved))))
