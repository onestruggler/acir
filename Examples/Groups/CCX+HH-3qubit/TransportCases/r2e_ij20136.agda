{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00647 as MV00647
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01984 as MV01984
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0136 ≈ K0136 • M2
proved = GL.•-cancelʳ {g = M2 • K0136} {g' = K0136 • M2} {h = p (s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01984.proved (MV00647.proved))) (trans (cong refl Base.proved) (move-product MV00647.proved (MV01984.proved))))
