{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00657 as MV00657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01254 as MV01254
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0236 ≈ K0236 • X14
proved = GL.•-cancelʳ {g = X14 • K0236} {g' = K0236 • X14} {h = p (s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01254.proved (MV00657.proved))) (trans (cong refl Base.proved) (move-product MV00657.proved (MV01254.proved))))
