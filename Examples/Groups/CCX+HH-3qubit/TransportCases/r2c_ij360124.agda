{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01564 as MV01564
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01565 as MV01565
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0124 ≈ K0124 • X36
proved = GL.•-cancelʳ {g = X36 • K0124} {g' = K0124 • X36} {h = p (s3 • s5)}
  (trans (sym (move-product MV01564.proved (MV01565.proved))) (trans (cong refl Base.proved) (move-product MV01565.proved (MV01564.proved))))
