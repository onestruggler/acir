{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij012345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00695 as MV00695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01034 as MV01034
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X01 • K2345 ≈ K2345 • X01
proved = GL.•-cancelʳ {g = X01 • K2345} {g' = K2345 • X01} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01034.proved (MV00695.proved))) (trans (cong refl Base.proved) (move-product MV00695.proved (MV01034.proved))))
