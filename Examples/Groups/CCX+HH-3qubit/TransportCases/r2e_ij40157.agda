{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02121 as MV02121
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02122 as MV02122
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0157 ≈ K0157 • M4
proved = GL.•-cancelʳ {g = M4 • K0157} {g' = K0157 • M4} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02121.proved (MV02122.proved))) (trans (cong refl Base.proved) (move-product MV02122.proved (MV02121.proved))))
