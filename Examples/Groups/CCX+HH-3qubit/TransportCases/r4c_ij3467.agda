{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij3467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; X47 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00707 as MV00707
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02820 as MV02820
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03029 as MV03029
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K3467 ≈ K3467 • X47
proved = GL.•-cancelʳ {g = X67 • K3467} {g' = K3467 • X47} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03029.proved (MV00707.proved))) (trans (cong refl Base.proved) (move-product MV00707.proved (MV02820.proved))))
