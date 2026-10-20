{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 as MV00685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01909 as MV01909
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1345 ≈ K1345 • M0
proved = GL.•-cancelʳ {g = M0 • K1345} {g' = K1345 • M0} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01909.proved (MV00685.proved))) (trans (cong refl Base.proved) (move-product MV00685.proved (MV01909.proved))))
