{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; X46 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00691 as MV00691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02756 as MV02756
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03013 as MV03013
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X56 • K1456 ≈ K1456 • X46
proved = GL.•-cancelʳ {g = X56 • K1456} {g' = K1456 • X46} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03013.proved (MV00691.proved))) (trans (cong refl Base.proved) (move-product MV00691.proved (MV02756.proved))))
