{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; M3 ; M6 ; X13 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00688 as MV00688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02743 as MV02743
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02744 as MV02744
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02745 as MV02745
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02746 as MV02746
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X13 • K1356 ≈ K1356 • X36 • M3 • M6
proved = GL.•-cancelʳ {g = X13 • K1356} {g' = K1356 • X36 • M3 • M6} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02743.proved (MV00688.proved))) (trans (cong refl Base.proved) (move-product MV00688.proved (move-product MV02744.proved (move-product MV02745.proved (MV02746.proved))))))
