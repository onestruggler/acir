{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2456 ; X46 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00701 as MV00701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02796 as MV02796
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03023 as MV03023
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X56 • K2456 ≈ K2456 • X46
proved = GL.•-cancelʳ {g = X56 • K2456} {g' = K2456 • X46} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03023.proved (MV00701.proved))) (trans (cong refl Base.proved) (move-product MV00701.proved (MV02796.proved))))
