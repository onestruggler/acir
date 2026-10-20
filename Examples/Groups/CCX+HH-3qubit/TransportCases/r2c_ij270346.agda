{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01493 as MV01493
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01494 as MV01494
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0346 ≈ K0346 • X27
proved = GL.•-cancelʳ {g = X27 • K0346} {g' = K0346 • X27} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01493.proved (MV01494.proved))) (trans (cong refl Base.proved) (move-product MV01494.proved (MV01493.proved))))
