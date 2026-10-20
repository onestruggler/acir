{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00665 as MV00665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01943 as MV01943
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0345 ≈ K0345 • M1
proved = GL.•-cancelʳ {g = M1 • K0345} {g' = K0345 • M1} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01943.proved (MV00665.proved))) (trans (cong refl Base.proved) (move-product MV00665.proved (MV01943.proved))))
