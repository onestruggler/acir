{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02073 as MV02073
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02074 as MV02074
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0467 ≈ K0467 • M3
proved = GL.•-cancelʳ {g = M3 • K0467} {g' = K0467 • M3} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02073.proved (MV02074.proved))) (trans (cong refl Base.proved) (move-product MV02074.proved (MV02073.proved))))
