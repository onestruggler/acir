{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij012356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2356 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00698 as MV00698
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01037 as MV01037
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X01 • K2356 ≈ K2356 • X01
proved = GL.•-cancelʳ {g = X01 • K2356} {g' = K2356 • X01} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01037.proved (MV00698.proved))) (trans (cong refl Base.proved) (move-product MV00698.proved (MV01037.proved))))
