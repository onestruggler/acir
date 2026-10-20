{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01234567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K4567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02381 as MV02381
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0123 • K4567 ≈ K4567 • K0123
proved = GL.•-cancelʳ {g = K0123 • K4567} {g' = K4567 • K0123} {h = p (ε)}
  (trans (sym (move-product MV00641.proved (MV02381.proved))) (trans (cong refl Base.proved) (move-product MV02381.proved (MV00641.proved))))
