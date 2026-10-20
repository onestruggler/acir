{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij04567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00632 as MV00632
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01933 as MV01933
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K4567 ≈ K4567 • M0
proved = GL.•-cancelʳ {g = M0 • K4567} {g' = K4567 • M0} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01933.proved (MV00632.proved))) (trans (cong refl Base.proved) (move-product MV00632.proved (MV01933.proved))))
