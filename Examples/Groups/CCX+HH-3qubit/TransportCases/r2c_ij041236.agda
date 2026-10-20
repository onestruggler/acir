{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij041236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; X04 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01094 as MV01094
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X04 • K1236 ≈ K1236 • X04
proved = GL.•-cancelʳ {g = X04 • K1236} {g' = K1236 • X04} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01094.proved (MV00677.proved))) (trans (cong refl Base.proved) (move-product MV00677.proved (MV01094.proved))))
