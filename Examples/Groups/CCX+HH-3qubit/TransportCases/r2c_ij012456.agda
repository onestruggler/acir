{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij012456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2456 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00701 as MV00701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01040 as MV01040
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X01 • K2456 ≈ K2456 • X01
proved = GL.•-cancelʳ {g = X01 • K2456} {g' = K2456 • X01} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01040.proved (MV00701.proved))) (trans (cong refl Base.proved) (move-product MV00701.proved (MV01040.proved))))
