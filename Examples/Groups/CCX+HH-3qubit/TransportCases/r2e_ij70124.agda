{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02313 as MV02313
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02314 as MV02314
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0124 ≈ K0124 • M7
proved = GL.•-cancelʳ {g = M7 • K0124} {g' = K0124 • M7} {h = p (s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02313.proved (MV02314.proved))) (trans (cong refl Base.proved) (move-product MV02314.proved (MV02313.proved))))
