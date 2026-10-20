{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; M2 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00698 as MV00698
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02940 as MV02940
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02941 as MV02941
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X35 • K2356 ≈ M2 • K2356 • M2 • K2356 • M2
proved = GL.•-cancelʳ {g = X35 • K2356} {g' = M2 • K2356 • M2 • K2356 • M2} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02940.proved (MV00698.proved))) (trans (cong refl Base.proved) (move-product MV02941.proved (move-product MV00698.proved (move-product MV02941.proved (move-product MV00698.proved (MV02941.proved)))))))
