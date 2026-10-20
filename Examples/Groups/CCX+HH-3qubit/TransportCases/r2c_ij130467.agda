{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01239 as MV01239
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01240 as MV01240
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K0467 ≈ K0467 • X13
proved = GL.•-cancelʳ {g = X13 • K0467} {g' = K0467 • X13} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01239.proved (MV01240.proved))) (trans (cong refl Base.proved) (move-product MV01240.proved (MV01239.proved))))
