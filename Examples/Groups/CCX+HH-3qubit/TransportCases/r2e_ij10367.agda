{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00670 as MV00670
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01948 as MV01948
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0367 ≈ K0367 • M1
proved = GL.•-cancelʳ {g = M1 • K0367} {g' = K0367 • M1} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01948.proved (MV00670.proved))) (trans (cong refl Base.proved) (move-product MV00670.proved (MV01948.proved))))
