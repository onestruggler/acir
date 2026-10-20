{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij362457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2457 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01592 as MV01592
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01593 as MV01593
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K2457 ≈ K2457 • X36
proved = GL.•-cancelʳ {g = X36 • K2457} {g' = K2457 • X36} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01592.proved (MV01593.proved))) (trans (cong refl Base.proved) (move-product MV01593.proved (MV01592.proved))))
