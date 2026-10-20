{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00032 as MV00032
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00246 as MV00246
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0123 ≈ K0123 • M5
proved = GL.•-cancelʳ {g = M5 • K0123} {g' = K0123 • M5} {h = p (s4)}
  (trans (sym (move-product MV00032.proved (MV00246.proved))) (trans (cong refl Base.proved) (move-product MV00246.proved (MV00032.proved))))
