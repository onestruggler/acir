{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij02467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01927 as MV01927
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K2467 ≈ K2467 • M0
proved = GL.•-cancelʳ {g = M0 • K2467} {g' = K2467 • M0} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01927.proved (MV00703.proved))) (trans (cong refl Base.proved) (move-product MV00703.proved (MV01927.proved))))
