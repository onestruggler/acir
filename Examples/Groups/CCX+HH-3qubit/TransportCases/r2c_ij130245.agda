{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00659 as MV00659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01229 as MV01229
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K0245 ≈ K0245 • X13
proved = GL.•-cancelʳ {g = X13 • K0245} {g' = K0245 • X13} {h = p (s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01229.proved (MV00659.proved))) (trans (cong refl Base.proved) (move-product MV00659.proved (MV01229.proved))))
