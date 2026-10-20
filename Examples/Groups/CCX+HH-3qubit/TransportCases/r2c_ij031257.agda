{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00683 as MV00683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01073 as MV01073
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1257 ≈ K1257 • X03
proved = GL.•-cancelʳ {g = X03 • K1257} {g' = K1257 • X03} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01073.proved (MV00683.proved))) (trans (cong refl Base.proved) (move-product MV00683.proved (MV01073.proved))))
