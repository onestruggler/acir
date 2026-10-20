{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij023467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0236 ; K2467 ; K3467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01784 as MV01784
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03080 as MV03080
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03081 as MV03081
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03082 as MV03082
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0234 • K2467 ≈ K3467 • K0236
proved = GL.•-cancelʳ {g = K0234 • K2467} {g' = K3467 • K0236} {h = p (s1 • s2 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01784.proved (MV03080.proved))) (trans (cong refl Base.proved) (move-product MV03081.proved (MV03082.proved))))
