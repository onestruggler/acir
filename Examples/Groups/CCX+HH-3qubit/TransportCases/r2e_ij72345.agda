{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij72345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02371 as MV02371
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02372 as MV02372
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K2345 ≈ K2345 • M7
proved = GL.•-cancelʳ {g = M7 • K2345} {g' = K2345 • M7} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02371.proved (MV02372.proved))) (trans (cong refl Base.proved) (move-product MV02372.proved (MV02371.proved))))
