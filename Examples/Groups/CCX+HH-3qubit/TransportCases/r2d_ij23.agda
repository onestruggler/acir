{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij23 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01826 as MV01826
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01827 as MV01827
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M2 • M3 ≈ M3 • M2
proved = GL.•-cancelʳ {g = M2 • M3} {g' = M3 • M2} {h = p (s1 • s0 • s3)}
  (trans (sym (move-product MV01826.proved (MV01827.proved))) (trans (cong refl Base.proved) (move-product MV01827.proved (MV01826.proved))))
