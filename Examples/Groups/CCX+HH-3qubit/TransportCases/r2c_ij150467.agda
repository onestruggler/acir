{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01297 as MV01297
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01298 as MV01298
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K0467 ≈ K0467 • X15
proved = GL.•-cancelʳ {g = X15 • K0467} {g' = K0467 • X15} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01297.proved (MV01298.proved))) (trans (cong refl Base.proved) (move-product MV01298.proved (MV01297.proved))))
