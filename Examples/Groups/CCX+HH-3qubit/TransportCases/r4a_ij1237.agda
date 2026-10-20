{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; M2 ; M7 ; X12 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00678 as MV00678
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02703 as MV02703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02704 as MV02704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02705 as MV02705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02706 as MV02706
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X12 • K1237 ≈ K1237 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X12 • K1237} {g' = K1237 • X27 • M2 • M7} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02703.proved (MV00678.proved))) (trans (cong refl Base.proved) (move-product MV00678.proved (move-product MV02704.proved (move-product MV02705.proved (MV02706.proved))))))
