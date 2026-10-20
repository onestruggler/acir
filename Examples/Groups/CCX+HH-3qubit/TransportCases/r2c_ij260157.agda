{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01459 as MV01459
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01460 as MV01460
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K0157 ≈ K0157 • X26
proved = GL.•-cancelʳ {g = X26 • K0157} {g' = K0157 • X26} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01459.proved (MV01460.proved))) (trans (cong refl Base.proved) (move-product MV01460.proved (MV01459.proved))))
