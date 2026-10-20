{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01241 as MV01241
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01242 as MV01242
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K0567 ≈ K0567 • X13
proved = GL.•-cancelʳ {g = X13 • K0567} {g' = K0567 • X13} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01241.proved (MV01242.proved))) (trans (cong refl Base.proved) (move-product MV01242.proved (MV01241.proved))))
