{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij01267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; M0 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00684 as MV00684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01908 as MV01908
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M0 • K1267 ≈ K1267 • M0
proved = GL.•-cancelʳ {g = M0 • K1267} {g' = K1267 • M0} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01908.proved (MV00684.proved))) (trans (cong refl Base.proved) (move-product MV00684.proved (MV01908.proved))))
