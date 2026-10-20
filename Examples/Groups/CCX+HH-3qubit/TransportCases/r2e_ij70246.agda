{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02339 as MV02339
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02340 as MV02340
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0246 ≈ K0246 • M7
proved = GL.•-cancelʳ {g = M7 • K0246} {g' = K0246 • M7} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02339.proved (MV02340.proved))) (trans (cong refl Base.proved) (move-product MV02340.proved (MV02339.proved))))
