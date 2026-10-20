{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01906 as MV01906
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1256 ≈ K1256 • M0
proved = GL.•-cancelʳ {g = M0 • K1256} {g' = K1256 • M0} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01906.proved (MV00682.proved))) (trans (cong refl Base.proved) (move-product MV00682.proved (MV01906.proved))))
