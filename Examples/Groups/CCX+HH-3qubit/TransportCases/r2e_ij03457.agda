{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij03457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3457 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00706 as MV00706
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01930 as MV01930
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K3457 ≈ K3457 • M0
proved = GL.•-cancelʳ {g = M0 • K3457} {g' = K3457 • M0} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01930.proved (MV00706.proved))) (trans (cong refl Base.proved) (move-product MV00706.proved (MV01930.proved))))
