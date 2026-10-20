{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij13467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01977 as MV01977
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01978 as MV01978
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K3467 ≈ K3467 • M1
proved = GL.•-cancelʳ {g = M1 • K3467} {g' = K3467 • M1} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01977.proved (MV01978.proved))) (trans (cong refl Base.proved) (move-product MV01978.proved (MV01977.proved))))
