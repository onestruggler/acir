{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij71256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02361 as MV02361
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02362 as MV02362
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K1256 ≈ K1256 • M7
proved = GL.•-cancelʳ {g = M7 • K1256} {g' = K1256 • M7} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02361.proved (MV02362.proved))) (trans (cong refl Base.proved) (move-product MV02362.proved (MV02361.proved))))
