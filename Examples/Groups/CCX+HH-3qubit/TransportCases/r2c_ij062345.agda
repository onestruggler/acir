{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij062345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01169 as MV01169
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01170 as MV01170
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K2345 ≈ K2345 • X06
proved = GL.•-cancelʳ {g = X06 • K2345} {g' = K2345 • X06} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01169.proved (MV01170.proved))) (trans (cong refl Base.proved) (move-product MV01170.proved (MV01169.proved))))
