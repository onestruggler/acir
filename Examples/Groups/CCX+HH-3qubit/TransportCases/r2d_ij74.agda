{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij74 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01894 as MV01894
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01895 as MV01895
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M7 • M4 ≈ M4 • M7
proved = GL.•-cancelʳ {g = M7 • M4} {g' = M4 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4)}
  (trans (sym (move-product MV01894.proved (MV01895.proved))) (trans (cong refl Base.proved) (move-product MV01895.proved (MV01894.proved))))
