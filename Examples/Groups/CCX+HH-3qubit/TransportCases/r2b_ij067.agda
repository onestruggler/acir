{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij067 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00771 as MV00771
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00772 as MV00772
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X06 • M7 ≈ M7 • X06
proved = GL.•-cancelʳ {g = X06 • M7} {g' = M7 • X06} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00771.proved (MV00772.proved))) (trans (cong refl Base.proved) (move-product MV00772.proved (MV00771.proved))))
