{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01237 as MV01237
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01238 as MV01238
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K0457 ≈ K0457 • X13
proved = GL.•-cancelʳ {g = X13 • K0457} {g' = K0457 • X13} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01237.proved (MV01238.proved))) (trans (cong refl Base.proved) (move-product MV01238.proved (MV01237.proved))))
