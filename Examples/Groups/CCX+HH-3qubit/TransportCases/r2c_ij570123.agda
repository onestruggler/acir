{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01741 as MV01741
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01742 as MV01742
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0123 ≈ K0123 • X57
proved = GL.•-cancelʳ {g = X57 • K0123} {g' = K0123 • X57} {h = p (s4 • s6 • s5)}
  (trans (sym (move-product MV01741.proved (MV01742.proved))) (trans (cong refl Base.proved) (move-product MV01742.proved (MV01741.proved))))
