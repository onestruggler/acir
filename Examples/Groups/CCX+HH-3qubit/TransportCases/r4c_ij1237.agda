{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; X27 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00678 as MV00678
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02704 as MV02704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03000 as MV03000
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X37 • K1237 ≈ K1237 • X27
proved = GL.•-cancelʳ {g = X37 • K1237} {g' = K1237 • X27} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03000.proved (MV00678.proved))) (trans (cong refl Base.proved) (move-product MV00678.proved (MV02704.proved))))
