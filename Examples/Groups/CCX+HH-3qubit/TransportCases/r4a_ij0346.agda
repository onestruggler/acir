{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; M3 ; M6 ; X03 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00666 as MV00666
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02655 as MV02655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02656 as MV02656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02657 as MV02657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02658 as MV02658
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X03 • K0346 ≈ K0346 • X36 • M3 • M6
proved = GL.•-cancelʳ {g = X03 • K0346} {g' = K0346 • X36 • M3 • M6} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02655.proved (MV00666.proved))) (trans (cong refl Base.proved) (move-product MV00666.proved (move-product MV02656.proved (move-product MV02657.proved (MV02658.proved))))))
