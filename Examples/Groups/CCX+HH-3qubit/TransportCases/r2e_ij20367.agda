{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02002 as MV02002
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02003 as MV02003
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0367 ≈ K0367 • M2
proved = GL.•-cancelʳ {g = M2 • K0367} {g' = K0367 • M2} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02002.proved (MV02003.proved))) (trans (cong refl Base.proved) (move-product MV02003.proved (MV02002.proved))))
