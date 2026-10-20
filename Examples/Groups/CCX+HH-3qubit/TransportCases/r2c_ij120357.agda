{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00669 as MV00669
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01213 as MV01213
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K0357 ≈ K0357 • X12
proved = GL.•-cancelʳ {g = X12 • K0357} {g' = K0357 • X12} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01213.proved (MV00669.proved))) (trans (cong refl Base.proved) (move-product MV00669.proved (MV01213.proved))))
