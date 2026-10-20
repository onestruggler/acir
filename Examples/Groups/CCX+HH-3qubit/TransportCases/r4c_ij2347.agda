{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2347 ; X37 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00697 as MV00697
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02780 as MV02780
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03019 as MV03019
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X47 • K2347 ≈ K2347 • X37
proved = GL.•-cancelʳ {g = X47 • K2347} {g' = K2347 • X37} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03019.proved (MV00697.proved))) (trans (cong refl Base.proved) (move-product MV00697.proved (MV02780.proved))))
