{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij023567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; K0236 ; K2567 ; K3567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01786 as MV01786
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03083 as MV03083
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03084 as MV03084
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03085 as MV03085
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0235 • K2567 ≈ K3567 • K0236
proved = GL.•-cancelʳ {g = K0235 • K2567} {g' = K3567 • K0236} {h = p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01786.proved (MV03083.proved))) (trans (cong refl Base.proved) (move-product MV03084.proved (MV03085.proved))))
