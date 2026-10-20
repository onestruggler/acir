{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02211 as MV02211
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02212 as MV02212
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0467 ≈ K0467 • M5
proved = GL.•-cancelʳ {g = M5 • K0467} {g' = K0467 • M5} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02211.proved (MV02212.proved))) (trans (cong refl Base.proved) (move-product MV02212.proved (MV02211.proved))))
