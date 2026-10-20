{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; M3 ; M6 ; X23 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00698 as MV00698
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02783 as MV02783
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02784 as MV02784
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02785 as MV02785
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02786 as MV02786
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X23 • K2356 ≈ K2356 • X36 • M3 • M6
proved = GL.•-cancelʳ {g = X23 • K2356} {g' = K2356 • X36 • M3 • M6} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02783.proved (MV00698.proved))) (trans (cong refl Base.proved) (move-product MV00698.proved (move-product MV02784.proved (move-product MV02785.proved (MV02786.proved))))))
