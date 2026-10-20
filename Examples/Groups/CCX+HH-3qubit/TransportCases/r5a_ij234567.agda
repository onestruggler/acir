{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij234567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; K2346 ; K3567 ; K4567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01800 as MV01800
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03110 as MV03110
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03111 as MV03111
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03112 as MV03112
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K2345 • K3567 ≈ K4567 • K2346
proved = GL.•-cancelʳ {g = K2345 • K3567} {g' = K4567 • K2346} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01800.proved (MV03110.proved))) (trans (cong refl Base.proved) (move-product MV03111.proved (MV03112.proved))))
