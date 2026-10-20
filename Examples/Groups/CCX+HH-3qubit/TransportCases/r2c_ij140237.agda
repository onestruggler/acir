{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; X14 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00658 as MV00658
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01255 as MV01255
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X14 • K0237 ≈ K0237 • X14
proved = GL.•-cancelʳ {g = X14 • K0237} {g' = K0237 • X14} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01255.proved (MV00658.proved))) (trans (cong refl Base.proved) (move-product MV00658.proved (MV01255.proved))))
