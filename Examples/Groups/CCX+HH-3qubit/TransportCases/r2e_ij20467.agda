{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02008 as MV02008
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02009 as MV02009
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0467 ≈ K0467 • M2
proved = GL.•-cancelʳ {g = M2 • K0467} {g' = K0467 • M2} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02008.proved (MV02009.proved))) (trans (cong refl Base.proved) (move-product MV02009.proved (MV02008.proved))))
