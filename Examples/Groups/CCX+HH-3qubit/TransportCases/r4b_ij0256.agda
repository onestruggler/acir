{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; M0 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02869 as MV02869
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02870 as MV02870
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X25 • K0256 ≈ M0 • K0256 • M0 • K0256 • M0
proved = GL.•-cancelʳ {g = X25 • K0256} {g' = M0 • K0256 • M0 • K0256 • M0} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02869.proved (MV00662.proved))) (trans (cong refl Base.proved) (move-product MV02870.proved (move-product MV00662.proved (move-product MV02870.proved (move-product MV00662.proved (MV02870.proved)))))))
