{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij50267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02203 as MV02203
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02204 as MV02204
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M5 • K0267 ≈ K0267 • M5
proved = GL.•-cancelʳ {g = M5 • K0267} {g' = K0267 • M5} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02203.proved (MV02204.proved))) (trans (cong refl Base.proved) (move-product MV02204.proved (MV02203.proved))))
