{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij250 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00878 as MV00878
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00879 as MV00879
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X25 • M0 ≈ M0 • X25
proved = GL.•-cancelʳ {g = X25 • M0} {g' = M0 • X25} {h = p (s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00878.proved (MV00879.proved))) (trans (cong refl Base.proved) (move-product MV00879.proved (MV00878.proved))))
