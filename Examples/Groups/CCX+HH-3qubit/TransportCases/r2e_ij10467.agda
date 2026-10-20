{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00673 as MV00673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01951 as MV01951
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0467 ≈ K0467 • M1
proved = GL.•-cancelʳ {g = M1 • K0467} {g' = K0467 • M1} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01951.proved (MV00673.proved))) (trans (cong refl Base.proved) (move-product MV00673.proved (MV01951.proved))))
