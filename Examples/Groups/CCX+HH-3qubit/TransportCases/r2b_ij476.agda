{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij476 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00996 as MV00996
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00997 as MV00997
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X47 • M6 ≈ M6 • X47
proved = GL.•-cancelʳ {g = X47 • M6} {g' = M6 • X47} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00996.proved (MV00997.proved))) (trans (cong refl Base.proved) (move-product MV00997.proved (MV00996.proved))))
