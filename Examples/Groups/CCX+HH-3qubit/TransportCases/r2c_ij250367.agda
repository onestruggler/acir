{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01435 as MV01435
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01436 as MV01436
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0367 ≈ K0367 • X25
proved = GL.•-cancelʳ {g = X25 • K0367} {g' = K0367 • X25} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01435.proved (MV01436.proved))) (trans (cong refl Base.proved) (move-product MV01436.proved (MV01435.proved))))
