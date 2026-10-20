{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02055 as MV02055
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02056 as MV02056
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0167 ≈ K0167 • M3
proved = GL.•-cancelʳ {g = M3 • K0167} {g' = K0167 • M3} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02055.proved (MV02056.proved))) (trans (cong refl Base.proved) (move-product MV02056.proved (MV02055.proved))))
