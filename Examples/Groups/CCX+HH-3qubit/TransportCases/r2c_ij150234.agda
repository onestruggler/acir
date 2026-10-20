{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01280 as MV01280
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K0234 ≈ K0234 • X15
proved = GL.•-cancelʳ {g = X15 • K0234} {g' = K0234 • X15} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV01280.proved (MV00655.proved))) (trans (cong refl Base.proved) (move-product MV00655.proved (MV01280.proved))))
