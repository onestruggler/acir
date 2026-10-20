{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00694 as MV00694
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01918 as MV01918
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1567 ≈ K1567 • M0
proved = GL.•-cancelʳ {g = M0 • K1567} {g' = K1567 • M0} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01918.proved (MV00694.proved))) (trans (cong refl Base.proved) (move-product MV00694.proved (MV01918.proved))))
