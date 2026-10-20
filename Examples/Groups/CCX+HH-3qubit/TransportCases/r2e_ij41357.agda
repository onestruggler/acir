{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1357 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02159 as MV02159
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02160 as MV02160
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1357 ≈ K1357 • M4
proved = GL.•-cancelʳ {g = M4 • K1357} {g' = K1357 • M4} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02159.proved (MV02160.proved))) (trans (cong refl Base.proved) (move-product MV02160.proved (MV02159.proved))))
