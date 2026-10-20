{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij20 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01822 as MV01822
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01823 as MV01823
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M2 • M0 ≈ M0 • M2
proved = GL.•-cancelʳ {g = M2 • M0} {g' = M0 • M2} {h = p (s1 • s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01822.proved (MV01823.proved))) (trans (cong refl Base.proved) (move-product MV01823.proved (MV01822.proved))))
