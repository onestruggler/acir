{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02341 as MV02341
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02342 as MV02342
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0256 ≈ K0256 • M7
proved = GL.•-cancelʳ {g = M7 • K0256} {g' = K0256 • M7} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02341.proved (MV02342.proved))) (trans (cong refl Base.proved) (move-product MV02342.proved (MV02341.proved))))
