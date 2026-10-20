{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij023567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01065 as MV01065
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01066 as MV01066
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X02 • K3567 ≈ K3567 • X02
proved = GL.•-cancelʳ {g = X02 • K3567} {g' = K3567 • X02} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01065.proved (MV01066.proved))) (trans (cong refl Base.proved) (move-product MV01066.proved (MV01065.proved))))
