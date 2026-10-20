{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01243567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K3567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00245 as MV00245
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00629 as MV00629
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0124 • K3567 ≈ K3567 • K0124
proved = GL.•-cancelʳ {g = K0124 • K3567} {g' = K3567 • K0124} {h = p (s3)}
  (trans (sym (move-product MV00245.proved (MV00629.proved))) (trans (cong refl Base.proved) (move-product MV00629.proved (MV00245.proved))))
