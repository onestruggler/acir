{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02107 as MV02107
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02108 as MV02108
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0125 ≈ K0125 • M4
proved = GL.•-cancelʳ {g = M4 • K0125} {g' = K0125 • M4} {h = p (s4 • s3 • s4)}
  (trans (sym (move-product MV02107.proved (MV02108.proved))) (trans (cong refl Base.proved) (move-product MV02108.proved (MV02107.proved))))
