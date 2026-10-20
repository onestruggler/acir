{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01809 as MV01809
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02312 as MV02312
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M7 • K0123 ≈ K0123 • M7
proved = GL.•-cancelʳ {g = M7 • K0123} {g' = K0123 • M7} {h = p (s6 • s5 • s4)}
  (trans (sym (move-product MV01809.proved (MV02312.proved))) (trans (cong refl Base.proved) (move-product MV02312.proved (MV01809.proved))))
