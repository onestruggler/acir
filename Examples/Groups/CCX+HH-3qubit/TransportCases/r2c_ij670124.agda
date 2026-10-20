{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01773 as MV01773
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01774 as MV01774
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0124 ≈ K0124 • X67
proved = GL.•-cancelʳ {g = X67 • K0124} {g' = K0124 • X67} {h = p (s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01773.proved (MV01774.proved))) (trans (cong refl Base.proved) (move-product MV01774.proved (MV01773.proved))))
