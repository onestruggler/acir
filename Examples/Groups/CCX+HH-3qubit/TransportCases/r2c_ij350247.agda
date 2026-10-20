{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01548 as MV01548
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01549 as MV01549
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0247 ≈ K0247 • X35
proved = GL.•-cancelʳ {g = X35 • K0247} {g' = K0247 • X35} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01548.proved (MV01549.proved))) (trans (cong refl Base.proved) (move-product MV01549.proved (MV01548.proved))))
