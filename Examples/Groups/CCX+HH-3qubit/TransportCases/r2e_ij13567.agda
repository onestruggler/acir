{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij13567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01979 as MV01979
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01980 as MV01980
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K3567 ≈ K3567 • M1
proved = GL.•-cancelʳ {g = M1 • K3567} {g' = K3567 • M1} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01979.proved (MV01980.proved))) (trans (cong refl Base.proved) (move-product MV01980.proved (MV01979.proved))))
