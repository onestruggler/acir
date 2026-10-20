{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01988 as MV01988
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0147 ≈ K0147 • M2
proved = GL.•-cancelʳ {g = M2 • K0147} {g' = K0147 • M2} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01988.proved (MV00651.proved))) (trans (cong refl Base.proved) (move-product MV00651.proved (MV01988.proved))))
