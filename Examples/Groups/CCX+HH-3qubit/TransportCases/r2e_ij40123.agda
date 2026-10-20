{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; M4 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01805 as MV01805
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M4 • K0123 ≈ K0123 • M4
proved = GL.•-cancelʳ {g = M4 • K0123} {g' = K0123 • M4} {h = p (ε)}
  (trans (sym (move-product MV01805.proved (MV00641.proved))) (trans (cong refl Base.proved) (move-product MV00641.proved (MV01805.proved))))
