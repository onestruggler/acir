{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij134567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K1346 ; K3567 ; K4567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01798 as MV01798
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03107 as MV03107
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03108 as MV03108
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03109 as MV03109
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K1345 • K3567 ≈ K4567 • K1346
proved = GL.•-cancelʳ {g = K1345 • K3567} {g' = K4567 • K1346} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01798.proved (MV03107.proved))) (trans (cong refl Base.proved) (move-product MV03108.proved (MV03109.proved))))
