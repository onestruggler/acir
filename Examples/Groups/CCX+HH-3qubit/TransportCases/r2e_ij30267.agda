{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02067 as MV02067
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02068 as MV02068
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0267 ≈ K0267 • M3
proved = GL.•-cancelʳ {g = M3 • K0267} {g' = K0267 • M3} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02067.proved (MV02068.proved))) (trans (cong refl Base.proved) (move-product MV02068.proved (MV02067.proved))))
