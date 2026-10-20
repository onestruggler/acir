{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij072 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00775 as MV00775
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00776 as MV00776
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X07 • M2 ≈ M2 • X07
proved = GL.•-cancelʳ {g = X07 • M2} {g' = M2 • X07} {h = p (s1 • s0 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00775.proved (MV00776.proved))) (trans (cong refl Base.proved) (move-product MV00776.proved (MV00775.proved))))
