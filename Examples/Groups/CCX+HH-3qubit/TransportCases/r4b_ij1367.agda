{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; M1 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00690 as MV00690
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02924 as MV02924
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02925 as MV02925
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X36 • K1367 ≈ M1 • K1367 • M1 • K1367 • M1
proved = GL.•-cancelʳ {g = X36 • K1367} {g' = M1 • K1367 • M1 • K1367 • M1} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02924.proved (MV00690.proved))) (trans (cong refl Base.proved) (move-product MV02925.proved (move-product MV00690.proved (move-product MV02925.proved (move-product MV00690.proved (MV02925.proved)))))))
