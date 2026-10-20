{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij472 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00990 as MV00990
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00991 as MV00991
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X47 • M2 ≈ M2 • X47
proved = GL.•-cancelʳ {g = X47 • M2} {g' = M2 • X47} {h = p (s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00990.proved (MV00991.proved))) (trans (cong refl Base.proved) (move-product MV00991.proved (MV00990.proved))))
