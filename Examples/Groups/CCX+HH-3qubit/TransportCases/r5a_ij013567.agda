{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij013567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; K0136 ; K1567 ; K3567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01780 as MV01780
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03068 as MV03068
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03069 as MV03069
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03070 as MV03070
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0135 • K1567 ≈ K3567 • K0136
proved = GL.•-cancelʳ {g = K0135 • K1567} {g' = K3567 • K0136} {h = p (s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01780.proved (MV03068.proved))) (trans (cong refl Base.proved) (move-product MV03069.proved (MV03070.proved))))
