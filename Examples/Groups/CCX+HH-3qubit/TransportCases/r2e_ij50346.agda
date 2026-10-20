{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02205 as MV02205
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02206 as MV02206
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0346 ≈ K0346 • M5
proved = GL.•-cancelʳ {g = M5 • K0346} {g' = K0346 • M5} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02205.proved (MV02206.proved))) (trans (cong refl Base.proved) (move-product MV02206.proved (MV02205.proved))))
