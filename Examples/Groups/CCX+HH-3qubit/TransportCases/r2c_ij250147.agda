{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01427 as MV01427
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01428 as MV01428
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0147 ≈ K0147 • X25
proved = GL.•-cancelʳ {g = X25 • K0147} {g' = K0147 • X25} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01427.proved (MV01428.proved))) (trans (cong refl Base.proved) (move-product MV01428.proved (MV01427.proved))))
