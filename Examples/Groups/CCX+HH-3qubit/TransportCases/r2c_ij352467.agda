{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij352467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01562 as MV01562
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01563 as MV01563
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K2467 ≈ K2467 • X35
proved = GL.•-cancelʳ {g = X35 • K2467} {g' = K2467 • X35} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01562.proved (MV01563.proved))) (trans (cong refl Base.proved) (move-product MV01563.proved (MV01562.proved))))
