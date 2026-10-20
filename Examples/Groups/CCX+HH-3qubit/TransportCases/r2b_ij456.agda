{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M6 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00970 as MV00970
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00971 as MV00971
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X45 • M6 ≈ M6 • X45
proved = GL.•-cancelʳ {g = X45 • M6} {g' = M6 • X45} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00970.proved (MV00971.proved))) (trans (cong refl Base.proved) (move-product MV00971.proved (MV00970.proved))))
