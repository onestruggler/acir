{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; M1 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00683 as MV00683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02910 as MV02910
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02911 as MV02911
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X25 • K1257 ≈ M1 • K1257 • M1 • K1257 • M1
proved = GL.•-cancelʳ {g = X25 • K1257} {g' = M1 • K1257 • M1 • K1257 • M1} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02910.proved (MV00683.proved))) (trans (cong refl Base.proved) (move-product MV02911.proved (move-product MV00683.proved (move-product MV02911.proved (move-product MV00683.proved (MV02911.proved)))))))
