{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1357 ; X37 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00689 as MV00689
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02748 as MV02748
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03011 as MV03011
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X57 • K1357 ≈ K1357 • X37
proved = GL.•-cancelʳ {g = X57 • K1357} {g' = K1357 • X37} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03011.proved (MV00689.proved))) (trans (cong refl Base.proved) (move-product MV00689.proved (MV02748.proved))))
