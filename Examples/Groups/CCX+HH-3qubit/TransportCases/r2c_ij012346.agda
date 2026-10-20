{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij012346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2346 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00696 as MV00696
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01035 as MV01035
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X01 • K2346 ≈ K2346 • X01
proved = GL.•-cancelʳ {g = X01 • K2346} {g' = K2346 • X01} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01035.proved (MV00696.proved))) (trans (cong refl Base.proved) (move-product MV00696.proved (MV01035.proved))))
