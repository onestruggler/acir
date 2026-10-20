{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01900 as MV01900
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1235 ≈ K1235 • M0
proved = GL.•-cancelʳ {g = M0 • K1235} {g' = K1235 • M0} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV01900.proved (MV00676.proved))) (trans (cong refl Base.proved) (move-product MV00676.proved (MV01900.proved))))
