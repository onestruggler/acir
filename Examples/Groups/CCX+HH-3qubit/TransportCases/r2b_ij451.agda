{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij451 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00964 as MV00964
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00965 as MV00965
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X45 • M1 ≈ M1 • X45
proved = GL.•-cancelʳ {g = X45 • M1} {g' = M1 • X45} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00964.proved (MV00965.proved))) (trans (cong refl Base.proved) (move-product MV00965.proved (MV00964.proved))))
