{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij012367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2367 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00700 as MV00700
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01039 as MV01039
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X01 • K2367 ≈ K2367 • X01
proved = GL.•-cancelʳ {g = X01 • K2367} {g' = K2367 • X01} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01039.proved (MV00700.proved))) (trans (cong refl Base.proved) (move-product MV00700.proved (MV01039.proved))))
