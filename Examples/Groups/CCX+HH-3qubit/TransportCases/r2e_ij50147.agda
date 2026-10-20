{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02189 as MV02189
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02190 as MV02190
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0147 ≈ K0147 • M5
proved = GL.•-cancelʳ {g = M5 • K0147} {g' = K0147 • M5} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02189.proved (MV02190.proved))) (trans (cong refl Base.proved) (move-product MV02190.proved (MV02189.proved))))
