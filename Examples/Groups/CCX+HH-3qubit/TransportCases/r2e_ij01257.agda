{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00683 as MV00683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01907 as MV01907
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1257 ≈ K1257 • M0
proved = GL.•-cancelʳ {g = M0 • K1257} {g' = K1257 • M0} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01907.proved (MV00683.proved))) (trans (cong refl Base.proved) (move-product MV00683.proved (MV01907.proved))))
