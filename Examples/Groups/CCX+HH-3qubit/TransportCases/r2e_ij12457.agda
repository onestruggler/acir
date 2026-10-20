{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij12457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2457 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01967 as MV01967
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01968 as MV01968
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K2457 ≈ K2457 • M1
proved = GL.•-cancelʳ {g = M1 • K2457} {g' = K2457 • M1} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01967.proved (MV01968.proved))) (trans (cong refl Base.proved) (move-product MV01968.proved (MV01967.proved))))
