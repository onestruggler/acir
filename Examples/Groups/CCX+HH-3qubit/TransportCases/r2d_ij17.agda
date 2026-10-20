{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij17 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01820 as MV01820
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01821 as MV01821
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M1 • M7 ≈ M7 • M1
proved = GL.•-cancelʳ {g = M1 • M7} {g' = M7 • M1} {h = p (s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01820.proved (MV01821.proved))) (trans (cong refl Base.proved) (move-product MV01821.proved (MV01820.proved))))
