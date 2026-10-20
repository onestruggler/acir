{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij31256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02083 as MV02083
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02084 as MV02084
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K1256 ≈ K1256 • M3
proved = GL.•-cancelʳ {g = M3 • K1256} {g' = K1256 • M3} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02083.proved (MV02084.proved))) (trans (cong refl Base.proved) (move-product MV02084.proved (MV02083.proved))))
