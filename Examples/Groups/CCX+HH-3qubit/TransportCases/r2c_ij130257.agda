{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01233 as MV01233
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K0257 ≈ K0257 • X13
proved = GL.•-cancelʳ {g = X13 • K0257} {g' = K0257 • X13} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01233.proved (MV00663.proved))) (trans (cong refl Base.proved) (move-product MV00663.proved (MV01233.proved))))
