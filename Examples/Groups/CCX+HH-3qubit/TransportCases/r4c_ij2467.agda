{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; X47 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02804 as MV02804
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03025 as MV03025
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K2467 ≈ K2467 • X47
proved = GL.•-cancelʳ {g = X67 • K2467} {g' = K2467 • X47} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03025.proved (MV00703.proved))) (trans (cong refl Base.proved) (move-product MV00703.proved (MV02804.proved))))
