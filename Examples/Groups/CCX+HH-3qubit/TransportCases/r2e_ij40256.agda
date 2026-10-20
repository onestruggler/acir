{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02131 as MV02131
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02132 as MV02132
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0256 ≈ K0256 • M4
proved = GL.•-cancelʳ {g = M4 • K0256} {g' = K0256 • M4} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02131.proved (MV02132.proved))) (trans (cong refl Base.proved) (move-product MV02132.proved (MV02131.proved))))
