{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00654 as MV00654
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01374 as MV01374
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K0167 ≈ K0167 • X23
proved = GL.•-cancelʳ {g = X23 • K0167} {g' = K0167 • X23} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01374.proved (MV00654.proved))) (trans (cong refl Base.proved) (move-product MV00654.proved (MV01374.proved))))
