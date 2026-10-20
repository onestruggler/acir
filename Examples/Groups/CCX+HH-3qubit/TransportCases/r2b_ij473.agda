{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij473 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00992 as MV00992
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00993 as MV00993
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X47 • M3 ≈ M3 • X47
proved = GL.•-cancelʳ {g = X47 • M3} {g' = M3 • X47} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00992.proved (MV00993.proved))) (trans (cong refl Base.proved) (move-product MV00993.proved (MV00992.proved))))
