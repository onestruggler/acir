{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij041257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; X04 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01098 as MV01098
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01099 as MV01099
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X04 • K1257 ≈ K1257 • X04
proved = GL.•-cancelʳ {g = X04 • K1257} {g' = K1257 • X04} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01098.proved (MV01099.proved))) (trans (cong refl Base.proved) (move-product MV01099.proved (MV01098.proved))))
