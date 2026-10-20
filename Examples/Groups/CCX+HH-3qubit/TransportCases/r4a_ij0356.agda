{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; M3 ; M6 ; X03 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00668 as MV00668
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02663 as MV02663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02664 as MV02664
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02665 as MV02665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02666 as MV02666
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X03 • K0356 ≈ K0356 • X36 • M3 • M6
proved = GL.•-cancelʳ {g = X03 • K0356} {g' = K0356 • X36 • M3 • M6} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02663.proved (MV00668.proved))) (trans (cong refl Base.proved) (move-product MV00668.proved (move-product MV02664.proved (move-product MV02665.proved (MV02666.proved))))))
