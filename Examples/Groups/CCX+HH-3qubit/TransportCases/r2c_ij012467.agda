{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij012467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01042 as MV01042
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X01 • K2467 ≈ K2467 • X01
proved = GL.•-cancelʳ {g = X01 • K2467} {g' = K2467 • X01} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01042.proved (MV00703.proved))) (trans (cong refl Base.proved) (move-product MV00703.proved (MV01042.proved))))
