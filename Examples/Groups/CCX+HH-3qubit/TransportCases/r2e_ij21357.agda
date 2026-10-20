{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1357 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02020 as MV02020
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02021 as MV02021
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K1357 ≈ K1357 • M2
proved = GL.•-cancelʳ {g = M2 • K1357} {g' = K1357 • M2} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02020.proved (MV02021.proved))) (trans (cong refl Base.proved) (move-product MV02021.proved (MV02020.proved))))
