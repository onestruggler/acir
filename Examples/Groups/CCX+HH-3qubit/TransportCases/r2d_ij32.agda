{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij32 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01839 as MV01839
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01840 as MV01840
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M3 • M2 ≈ M2 • M3
proved = GL.•-cancelʳ {g = M3 • M2} {g' = M2 • M3} {h = p (s2 • s1 • s0 • s3)}
  (trans (sym (move-product MV01839.proved (MV01840.proved))) (trans (cong refl Base.proved) (move-product MV01840.proved (MV01839.proved))))
