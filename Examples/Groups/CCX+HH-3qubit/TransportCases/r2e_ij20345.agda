{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01992 as MV01992
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01993 as MV01993
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0345 ≈ K0345 • M2
proved = GL.•-cancelʳ {g = M2 • K0345} {g' = K0345 • M2} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s4)}
  (trans (sym (move-product MV01992.proved (MV01993.proved))) (trans (cong refl Base.proved) (move-product MV01993.proved (MV01992.proved))))
