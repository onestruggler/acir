{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01807 as MV01807
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02243 as MV02243
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0123 ≈ K0123 • M6
proved = GL.•-cancelʳ {g = M6 • K0123} {g' = K0123 • M6} {h = p (s5 • s4)}
  (trans (sym (move-product MV01807.proved (MV02243.proved))) (trans (cong refl Base.proved) (move-product MV02243.proved (MV01807.proved))))
