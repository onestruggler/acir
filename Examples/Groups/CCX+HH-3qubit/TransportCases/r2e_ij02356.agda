{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij02356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00698 as MV00698
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01922 as MV01922
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K2356 ≈ K2356 • M0
proved = GL.•-cancelʳ {g = M0 • K2356} {g' = K2356 • M0} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01922.proved (MV00698.proved))) (trans (cong refl Base.proved) (move-product MV00698.proved (MV01922.proved))))
