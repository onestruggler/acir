{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij53467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02241 as MV02241
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02242 as MV02242
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K3467 ≈ K3467 • M5
proved = GL.•-cancelʳ {g = M5 • K3467} {g' = K3467 • M5} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02241.proved (MV02242.proved))) (trans (cong refl Base.proved) (move-product MV02242.proved (MV02241.proved))))
