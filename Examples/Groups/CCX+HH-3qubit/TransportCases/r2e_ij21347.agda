{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij21347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02016 as MV02016
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02017 as MV02017
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K1347 ≈ K1347 • M2
proved = GL.•-cancelʳ {g = M2 • K1347} {g' = K1347 • M2} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02016.proved (MV02017.proved))) (trans (cong refl Base.proved) (move-product MV02017.proved (MV02016.proved))))
