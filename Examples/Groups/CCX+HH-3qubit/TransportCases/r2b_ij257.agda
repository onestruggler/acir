{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00888 as MV00888
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00889 as MV00889
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X25 • M7 ≈ M7 • X25
proved = GL.•-cancelʳ {g = X25 • M7} {g' = M7 • X25} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00888.proved (MV00889.proved))) (trans (cong refl Base.proved) (move-product MV00889.proved (MV00888.proved))))
