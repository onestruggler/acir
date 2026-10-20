{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; X47 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00693 as MV00693
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02764 as MV02764
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03015 as MV03015
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K1467 ≈ K1467 • X47
proved = GL.•-cancelʳ {g = X67 • K1467} {g' = K1467 • X47} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03015.proved (MV00693.proved))) (trans (cong refl Base.proved) (move-product MV00693.proved (MV02764.proved))))
