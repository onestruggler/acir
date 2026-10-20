{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01457 as MV01457
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01458 as MV01458
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K0147 ≈ K0147 • X26
proved = GL.•-cancelʳ {g = X26 • K0147} {g' = K0147 • X26} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01457.proved (MV01458.proved))) (trans (cong refl Base.proved) (move-product MV01458.proved (MV01457.proved))))
