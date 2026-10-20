{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij72 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01891 as MV01891
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01892 as MV01892
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M7 • M2 ≈ M2 • M7
proved = GL.•-cancelʳ {g = M7 • M2} {g' = M2 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3)}
  (trans (sym (move-product MV01891.proved (MV01892.proved))) (trans (cong refl Base.proved) (move-product MV01892.proved (MV01891.proved))))
