{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij03456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00705 as MV00705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01929 as MV01929
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K3456 ≈ K3456 • M0
proved = GL.•-cancelʳ {g = M0 • K3456} {g' = K3456 • M0} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01929.proved (MV00705.proved))) (trans (cong refl Base.proved) (move-product MV00705.proved (MV01929.proved))))
