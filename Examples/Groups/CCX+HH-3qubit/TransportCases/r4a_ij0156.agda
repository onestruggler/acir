{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; M1 ; M6 ; X01 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02599 as MV02599
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02600 as MV02600
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02601 as MV02601
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02602 as MV02602
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0156 ≈ K0156 • X16 • M1 • M6
proved = GL.•-cancelʳ {g = X01 • K0156} {g' = K0156 • X16 • M1 • M6} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02599.proved (MV00652.proved))) (trans (cong refl Base.proved) (move-product MV00652.proved (move-product MV02600.proved (move-product MV02601.proved (MV02602.proved))))))
