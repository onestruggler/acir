{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij41267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02155 as MV02155
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02156 as MV02156
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K1267 ≈ K1267 • M4
proved = GL.•-cancelʳ {g = M4 • K1267} {g' = K1267 • M4} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02155.proved (MV02156.proved))) (trans (cong refl Base.proved) (move-product MV02156.proved (MV02155.proved))))
