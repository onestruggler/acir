{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02012 as MV02012
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02013 as MV02013
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K1345 ≈ K1345 • M2
proved = GL.•-cancelʳ {g = M2 • K1345} {g' = K1345 • M2} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV02012.proved (MV02013.proved))) (trans (cong refl Base.proved) (move-product MV02013.proved (MV02012.proved))))
