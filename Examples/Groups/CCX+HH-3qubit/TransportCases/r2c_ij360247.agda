{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360247 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0247 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01578 as MV01578
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01579 as MV01579
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0247 ≈ K0247 • X36
proved = GL.•-cancelʳ {g = X36 • K0247} {g' = K0247 • X36} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01578.proved (MV01579.proved))) (trans (cong refl Base.proved) (move-product MV01579.proved (MV01578.proved))))
