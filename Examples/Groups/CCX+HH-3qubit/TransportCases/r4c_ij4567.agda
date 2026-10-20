{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij4567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00632 as MV00632
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02828 as MV02828
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03031 as MV03031
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K4567 ≈ K4567 • X57
proved = GL.•-cancelʳ {g = X67 • K4567} {g' = K4567 • X57} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03031.proved (MV00632.proved))) (trans (cong refl Base.proved) (move-product MV00632.proved (MV02828.proved))))
