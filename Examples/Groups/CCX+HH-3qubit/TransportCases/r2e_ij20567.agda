{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02010 as MV02010
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02011 as MV02011
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0567 ≈ K0567 • M2
proved = GL.•-cancelʳ {g = M2 • K0567} {g' = K0567 • M2} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02010.proved (MV02011.proved))) (trans (cong refl Base.proved) (move-product MV02011.proved (MV02010.proved))))
