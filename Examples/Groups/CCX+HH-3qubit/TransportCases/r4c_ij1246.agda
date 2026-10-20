{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; X26 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00680 as MV00680
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02712 as MV02712
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03002 as MV03002
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X46 • K1246 ≈ K1246 • X26
proved = GL.•-cancelʳ {g = X46 • K1246} {g' = K1246 • X26} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03002.proved (MV00680.proved))) (trans (cong refl Base.proved) (move-product MV00680.proved (MV02712.proved))))
