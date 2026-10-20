{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02143 as MV02143
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02144 as MV02144
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0567 ≈ K0567 • M4
proved = GL.•-cancelʳ {g = M4 • K0567} {g' = K0567 • M4} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02143.proved (MV02144.proved))) (trans (cong refl Base.proved) (move-product MV02144.proved (MV02143.proved))))
