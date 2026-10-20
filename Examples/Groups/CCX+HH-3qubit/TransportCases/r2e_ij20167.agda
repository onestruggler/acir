{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00654 as MV00654
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01991 as MV01991
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0167 ≈ K0167 • M2
proved = GL.•-cancelʳ {g = M2 • K0167} {g' = K0167 • M2} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01991.proved (MV00654.proved))) (trans (cong refl Base.proved) (move-product MV00654.proved (MV01991.proved))))
