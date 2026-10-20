{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; M3 ; M5 ; X03 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00665 as MV00665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02651 as MV02651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02652 as MV02652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02653 as MV02653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02654 as MV02654
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X03 • K0345 ≈ K0345 • X35 • M3 • M5
proved = GL.•-cancelʳ {g = X03 • K0345} {g' = K0345 • X35 • M3 • M5} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02651.proved (MV00665.proved))) (trans (cong refl Base.proved) (move-product MV00665.proved (move-product MV02652.proved (move-product MV02653.proved (MV02654.proved))))))
