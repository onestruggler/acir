{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_ij0123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; _•_ ; _≈_ ; cong ; left-unit ; move-product ; p ; refl ; right-unit ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 as Base

proved : K0123 • K0123 ≈ ε
proved = GL.•-cancelʳ {g = K0123 • K0123} {g' = ε} {h = p (ε)}
  (trans (sym (move-product MV00641.proved (MV00641.proved))) (trans (cong refl Base.proved) (trans right-unit (sym left-unit))))
