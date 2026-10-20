{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01941 as MV01941
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0257 ≈ K0257 • M1
proved = GL.•-cancelʳ {g = M1 • K0257} {g' = K0257 • M1} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01941.proved (MV00663.proved))) (trans (cong refl Base.proved) (move-product MV00663.proved (MV01941.proved))))
