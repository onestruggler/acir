{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij470 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00986 as MV00986
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00987 as MV00987
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X47 • M0 ≈ M0 • X47
proved = GL.•-cancelʳ {g = X47 • M0} {g' = M0 • X47} {h = p (s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00986.proved (MV00987.proved))) (trans (cong refl Base.proved) (move-product MV00987.proved (MV00986.proved))))
