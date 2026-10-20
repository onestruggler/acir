{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00828 as MV00828
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00829 as MV00829
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X15 • M7 ≈ M7 • X15
proved = GL.•-cancelʳ {g = X15 • M7} {g' = M7 • X15} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00828.proved (MV00829.proved))) (trans (cong refl Base.proved) (move-product MV00829.proved (MV00828.proved))))
