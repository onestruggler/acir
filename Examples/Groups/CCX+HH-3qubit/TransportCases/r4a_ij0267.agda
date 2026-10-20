{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; M2 ; M7 ; X02 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00664 as MV00664
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02647 as MV02647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02648 as MV02648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02649 as MV02649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02650 as MV02650
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X02 • K0267 ≈ K0267 • X27 • M2 • M7
proved = GL.•-cancelʳ {g = X02 • K0267} {g' = K0267 • X27 • M2 • M7} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02647.proved (MV00664.proved))) (trans (cong refl Base.proved) (move-product MV00664.proved (move-product MV02648.proved (move-product MV02649.proved (MV02650.proved))))))
