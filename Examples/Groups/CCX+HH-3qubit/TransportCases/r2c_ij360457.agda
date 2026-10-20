{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0457 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01582 as MV01582
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01583 as MV01583
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0457 ≈ K0457 • X36
proved = GL.•-cancelʳ {g = X36 • K0457} {g' = K0457 • X36} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01582.proved (MV01583.proved))) (trans (cong refl Base.proved) (move-product MV01583.proved (MV01582.proved))))
