{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01804 as MV01804
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0134 ≈ K0134 • M2
proved = GL.•-cancelʳ {g = M2 • K0134} {g' = K0134 • M2} {h = p (s2 • s3)}
  (trans (sym (move-product MV01804.proved (MV00645.proved))) (trans (cong refl Base.proved) (move-product MV00645.proved (MV01804.proved))))
