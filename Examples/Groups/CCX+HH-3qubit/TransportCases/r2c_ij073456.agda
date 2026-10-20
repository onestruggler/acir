{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij073456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01207 as MV01207
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01208 as MV01208
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X07 • K3456 ≈ K3456 • X07
proved = GL.•-cancelʳ {g = X07 • K3456} {g' = K3456 • X07} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01207.proved (MV01208.proved))) (trans (cong refl Base.proved) (move-product MV01208.proved (MV01207.proved))))
