{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01580 as MV01580
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01581 as MV01581
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0257 ≈ K0257 • X36
proved = GL.•-cancelʳ {g = X36 • K0257} {g' = K0257 • X36} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01580.proved (MV01581.proved))) (trans (cong refl Base.proved) (move-product MV01581.proved (MV01580.proved))))
