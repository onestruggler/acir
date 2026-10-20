{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij150 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00818 as MV00818
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00819 as MV00819
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X15 • M0 ≈ M0 • X15
proved = GL.•-cancelʳ {g = X15 • M0} {g' = M0 • X15} {h = p (s4 • s3 • s2)}
  (trans (sym (move-product MV00818.proved (MV00819.proved))) (trans (cong refl Base.proved) (move-product MV00819.proved (MV00818.proved))))
