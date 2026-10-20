{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij41 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01850 as MV01850
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01851 as MV01851
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M4 • M1 ≈ M1 • M4
proved = GL.•-cancelʳ {g = M4 • M1} {g' = M1 • M4} {h = p (s3 • s2 • s1 • s0 • s2 • s3)}
  (trans (sym (move-product MV01850.proved (MV01851.proved))) (trans (cong refl Base.proved) (move-product MV01851.proved (MV01850.proved))))
