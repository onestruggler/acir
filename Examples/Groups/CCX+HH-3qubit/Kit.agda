------------------------------------------------------------------------
-- The vocabulary of the generated certificates, and nothing else.
--
-- An interface records the scope of every module its module imports,
-- not only the names it uses: a certificate that opened Syntactics,
-- Frames, FrameWords and Engine (Engine re-exports Presentation.Base's
-- congruence, Syntactics re-exports Word.Base) took 50-65 kB on disk
-- for a proof of one line, and the eight thousand of them are loaded
-- together by TwoLevel and the presentation.  A certificate imports
-- this module, or FrameKit, restricted to the names it uses
-- (`import Kit as K using (…)`, then `open K`), and its interface
-- records those names alone.  This module has the gates, the words of
-- Figure 4, the rules and the congruence; FrameKit adds the frames.
-- The two are separate because Frames imports the permutation
-- certificates, which import this module.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Kit where

open import Data.Fin.Base public using (zero ; suc)
open import Examples.Groups.CCX+HH-3qubit.Syntactics public
  using (_≈_ ; _•_ ; ε
        ; CCX01 ; CCX02 ; CCX12 ; CCZ ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21
        ; CZ01 ; CZ02 ; CZ12 ; K01 ; K12 ; NK ; SWAP01 ; SWAP02 ; SWAP12
        ; X0 ; X1 ; X2 ; Z0 ; Z1 ; Z2
        ; k0124 ; k1345 ; k2345 ; k4567 ; m0 ; m1 ; m3 ; m4 ; rho
        ; t01 ; t04 ; t12 ; t13 ; t23 ; t34 ; t45 ; t56 ; t67
        ; r001 ; r002 ; r003 ; r004 ; r005 ; r006 ; r007 ; r008 ; r009 ; r010
        ; r011 ; r012 ; r013 ; r014 ; r015 ; r016 ; r017 ; r018 ; r019 ; r020
        ; r021 ; r022 ; r023 ; r024 ; r025 ; r026 ; r027 ; r028 ; r029 ; r030
        ; r031 ; r032 ; r033 ; r034 ; r035 ; r036 ; r037 ; r038 ; r039 ; r040
        ; r041 ; r042 ; r043 ; r044 ; r045 ; r046 ; r083 ; r084 ; r085 ; r086
        ; r087 ; r088 ; r089 ; r090 ; r091 ; r092 ; r093 ; r094 ; r095 ; r096
        ; r097 ; r098 ; r099 ; r100 ; r101)
open import Examples.Groups.CCX+HH-3qubit.Engine public
  using (refl ; sym ; trans ; cong ; axiom ; left-unit ; right-unit
        ; by-assoc ; by-assoc-and ; under)

module Eq where
  open import Relation.Binary.PropositionalEquality public using (refl)
