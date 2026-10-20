{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij15 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01816 as MV01816
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01817 as MV01817
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M1 • M5 ≈ M5 • M1
proved = GL.•-cancelʳ {g = M1 • M5} {g' = M5 • M1} {h = p (s0 • s4)}
  (trans (sym (move-product MV01816.proved (MV01817.proved))) (trans (cong refl Base.proved) (move-product MV01817.proved (MV01816.proved))))
