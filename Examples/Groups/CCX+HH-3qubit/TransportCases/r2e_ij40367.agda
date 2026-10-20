{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02141 as MV02141
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02142 as MV02142
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0367 ≈ K0367 • M4
proved = GL.•-cancelʳ {g = M4 • K0367} {g' = K0367 • M4} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02141.proved (MV02142.proved))) (trans (cong refl Base.proved) (move-product MV02142.proved (MV02141.proved))))
