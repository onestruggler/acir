{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij243567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01418 as MV01418
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01419 as MV01419
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K3567 ≈ K3567 • X24
proved = GL.•-cancelʳ {g = X24 • K3567} {g' = K3567 • X24} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01418.proved (MV01419.proved))) (trans (cong refl Base.proved) (move-product MV01419.proved (MV01418.proved))))
