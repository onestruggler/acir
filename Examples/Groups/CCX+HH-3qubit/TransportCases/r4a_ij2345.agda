{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2345 ; M3 ; M5 ; X23 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00695 as MV00695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02771 as MV02771
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02772 as MV02772
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02773 as MV02773
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02774 as MV02774
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X23 • K2345 ≈ K2345 • X35 • M3 • M5
proved = GL.•-cancelʳ {g = X23 • K2345} {g' = K2345 • X35 • M3 • M5} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02771.proved (MV00695.proved))) (trans (cong refl Base.proved) (move-product MV00695.proved (move-product MV02772.proved (move-product MV02773.proved (MV02774.proved))))))
