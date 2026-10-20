{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij10346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00666 as MV00666
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01944 as MV01944
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K0346 ≈ K0346 • M1
proved = GL.•-cancelʳ {g = M1 • K0346} {g' = K0346 • M1} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01944.proved (MV00666.proved))) (trans (cong refl Base.proved) (move-product MV00666.proved (MV01944.proved))))
