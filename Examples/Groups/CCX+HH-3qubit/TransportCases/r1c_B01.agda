{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1c_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; _•_ ; _≈_ ; cong ; left-unit ; module GL ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00632)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R084)

module r1c_ij4567 where

  proved : K4567 • K4567 ≈ ε
  proved = GL.•-cancelʳ {g = K4567 • K4567} {g' = ε} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00632.proved (MV00632.proved))) (trans (cong refl R084.proved) (trans right-unit (sym left-unit))))
