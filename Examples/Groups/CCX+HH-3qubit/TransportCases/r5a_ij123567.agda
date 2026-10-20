{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij123567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; K1236 ; K2567 ; K3567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01794 as MV01794
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03101 as MV03101
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03102 as MV03102
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03103 as MV03103
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K1235 • K2567 ≈ K3567 • K1236
proved = GL.•-cancelʳ {g = K1235 • K2567} {g' = K3567 • K1236} {h = p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01794.proved (MV03101.proved))) (trans (cong refl Base.proved) (move-product MV03102.proved (MV03103.proved))))
