{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij032 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00727 as MV00727
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00728 as MV00728
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X03 • M2 ≈ M2 • X03
proved = GL.•-cancelʳ {g = X03 • M2} {g' = M2 • X03} {h = p (s1 • s0 • s2)}
  (trans (sym (move-product MV00727.proved (MV00728.proved))) (trans (cong refl Base.proved) (move-product MV00728.proved (MV00727.proved))))
