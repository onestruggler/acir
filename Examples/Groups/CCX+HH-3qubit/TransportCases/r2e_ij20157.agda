{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01990 as MV01990
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0157 ≈ K0157 • M2
proved = GL.•-cancelʳ {g = M2 • K0157} {g' = K0157 • M2} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01990.proved (MV00653.proved))) (trans (cong refl Base.proved) (move-product MV00653.proved (MV01990.proved))))
