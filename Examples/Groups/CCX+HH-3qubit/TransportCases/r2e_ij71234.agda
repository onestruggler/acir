{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij71234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02351 as MV02351
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02352 as MV02352
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K1234 ≈ K1234 • M7
proved = GL.•-cancelʳ {g = M7 • K1234} {g' = K1234 • M7} {h = p (s0 • s1 • s2 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02351.proved (MV02352.proved))) (trans (cong refl Base.proved) (move-product MV02352.proved (MV02351.proved))))
