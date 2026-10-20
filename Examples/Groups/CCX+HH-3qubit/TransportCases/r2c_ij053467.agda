{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij053467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; X05 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01147 as MV01147
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01148 as MV01148
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X05 • K3467 ≈ K3467 • X05
proved = GL.•-cancelʳ {g = X05 • K3467} {g' = K3467 • X05} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01147.proved (MV01148.proved))) (trans (cong refl Base.proved) (move-product MV01148.proved (MV01147.proved))))
