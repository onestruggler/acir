{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij53 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00638 as MV00638
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01867 as MV01867
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M5 • M3 ≈ M3 • M5
proved = GL.•-cancelʳ {g = M5 • M3} {g' = M3 • M5} {h = p (s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00638.proved (MV01867.proved))) (trans (cong refl Base.proved) (move-product MV01867.proved (MV00638.proved))))
