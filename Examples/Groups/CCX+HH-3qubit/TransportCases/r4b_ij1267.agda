{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; M1 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00684 as MV00684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02912 as MV02912
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02913 as MV02913
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X26 • K1267 ≈ M1 • K1267 • M1 • K1267 • M1
proved = GL.•-cancelʳ {g = X26 • K1267} {g' = M1 • K1267 • M1 • K1267 • M1} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02912.proved (MV00684.proved))) (trans (cong refl Base.proved) (move-product MV02913.proved (move-product MV00684.proved (move-product MV02913.proved (move-product MV00684.proved (MV02913.proved)))))))
