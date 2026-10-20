{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij034567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; K0346 ; K3567 ; K4567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01790 as MV01790
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03089 as MV03089
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03090 as MV03090
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03091 as MV03091
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0345 • K3567 ≈ K4567 • K0346
proved = GL.•-cancelʳ {g = K0345 • K3567} {g' = K4567 • K0346} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01790.proved (MV03089.proved))) (trans (cong refl Base.proved) (move-product MV03090.proved (MV03091.proved))))
