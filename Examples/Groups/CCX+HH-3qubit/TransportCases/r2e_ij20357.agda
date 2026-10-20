{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02000 as MV02000
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02001 as MV02001
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0357 ≈ K0357 • M2
proved = GL.•-cancelʳ {g = M2 • K0357} {g' = K0357 • M2} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02000.proved (MV02001.proved))) (trans (cong refl Base.proved) (move-product MV02001.proved (MV02000.proved))))
