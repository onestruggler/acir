{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij3456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; X46 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00705 as MV00705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02812 as MV02812
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03027 as MV03027
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X56 • K3456 ≈ K3456 • X46
proved = GL.•-cancelʳ {g = X56 • K3456} {g' = K3456 • X46} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03027.proved (MV00705.proved))) (trans (cong refl Base.proved) (move-product MV00705.proved (MV02812.proved))))
