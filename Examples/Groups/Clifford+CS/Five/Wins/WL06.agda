------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL06 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

wl0907 : Complete 4 → ⟪ (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl0907 c4 = lw0 c4 (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl0908 : Complete 4 → ⟪ (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl0908 c4 = lw0 c4 (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl0909 : Complete 4 → ⟪ (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wl0909 c4 = lw0 c4 (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wl0910 : Complete 4 → ⟪ (CS14 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS14 ∷ []) ⟫ʷ
wl0910 c4 = lw0 c4 (CS14 ∷ S4 ∷ []) (S4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0911 : Complete 4 → ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ
wl0911 c4 = lw0 c4 (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ []) tt tt Eq.refl

wl0912 : Complete 4 → ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ
wl0912 c4 = lw0 c4 (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ []) tt tt Eq.refl

wl0913 : Complete 4 → ⟪ (CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK41 ∷ []) ⟫ʷ
wl0913 c4 = lw0 c4 (CK41 ∷ S4 ∷ []) (S4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0914 : Complete 4 → ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ
wl0914 c4 = lw0 c4 (CK41 ∷ CS24 ∷ []) (CS24 ∷ CK41 ∷ []) tt tt Eq.refl

wl0915 : Complete 4 → ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ
wl0915 c4 = lw0 c4 (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ []) tt tt Eq.refl

wl0916 : Complete 4 → ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ
wl0916 c4 = lw0 c4 (CK41 ∷ CS34 ∷ []) (CS34 ∷ CK41 ∷ []) tt tt Eq.refl

wl0917 : Complete 4 → ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ
wl0917 c4 = lw0 c4 (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ []) tt tt Eq.refl

wl0918 : Complete 4 → ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ
wl0918 c4 = lw0 c4 (CS24 ∷ S4 ∷ []) (S4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0919 : Complete 4 → ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ
wl0919 c4 = lw0 c4 (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ []) tt tt Eq.refl

wl0920 : Complete 4 → ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ
wl0920 c4 = lw0 c4 (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ []) tt tt Eq.refl

wl0921 : Complete 4 → ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ
wl0921 c4 = lw0 c4 (CK42 ∷ S4 ∷ []) (S4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0922 : Complete 4 → ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ
wl0922 c4 = lw0 c4 (CK42 ∷ CS34 ∷ []) (CS34 ∷ CK42 ∷ []) tt tt Eq.refl

wl0923 : Complete 4 → ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ
wl0923 c4 = lw0 c4 (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ []) tt tt Eq.refl

wl0924 : Complete 4 → ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ
wl0924 c4 = lw0 c4 (CS34 ∷ S4 ∷ []) (S4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0925 : Complete 4 → ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ
wl0925 c4 = lw0 c4 (CK43 ∷ S4 ∷ []) (S4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0926 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0926 c4 = lw0 c4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0927 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0927 c4 = lw0 c4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0928 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0928 c4 = lw0 c4 (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0929 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0929 c4 = lw0 c4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0930 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0930 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0931 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0931 c4 = lw0 c4 (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0932 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0932 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0933 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0933 c4 = lw0 c4 (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0934 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0934 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0935 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0935 c4 = lw0 c4 (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0936 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0936 c4 = lw0 c4 (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0937 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0937 c4 = lw0 c4 (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0938 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0938 c4 = lw0 c4 (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0939 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0939 c4 = lw0 c4 (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0940 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0940 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0941 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0941 c4 = lw0 c4 (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0942 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0942 c4 = lw0 c4 (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0943 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0943 c4 = lw0 c4 (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0944 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0944 c4 = lw0 c4 (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0945 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0945 c4 = lw0 c4 (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0946 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0946 c4 = lw0 c4 (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0947 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0947 c4 = lw0 c4 (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0948 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0948 c4 = lw0 c4 (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0949 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0949 c4 = lw0 c4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0950 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0950 c4 = lw0 c4 (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0951 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0951 c4 = lw0 c4 (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0952 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0952 c4 = lw0 c4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0953 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0953 c4 = lw0 c4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0954 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0954 c4 = lw0 c4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0955 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0955 c4 = lw0 c4 (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0956 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wl0956 c4 = lw0 c4 (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wl0957 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0957 c4 = lw0 c4 (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0958 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wl0958 c4 = lw0 c4 (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wl0959 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wl0959 c4 = lw0 c4 (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wl0960 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0960 c4 = lw0 c4 (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0961 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0961 c4 = lw0 c4 (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0962 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0962 c4 = lw0 c4 (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0963 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ []) ⟫ʷ
wl0963 c4 = lw0 c4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι1 ∷ []) tt tt Eq.refl

wl0964 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (ι2 ∷ []) ⟫ʷ
wl0964 c4 = lw0 c4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι2 ∷ []) tt tt Eq.refl

wl0965 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ []) ⟫ʷ
wl0965 c4 = lw0 c4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι3 ∷ []) tt tt Eq.refl

wl0966 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (ι4 ∷ []) ⟫ʷ
wl0966 c4 = lw0 c4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι4 ∷ []) tt tt Eq.refl

wl0967 : Complete 4 → ⟪ (S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wl0967 c4 = lw0 c4 (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wl0968 : Complete 4 → ⟪ (K2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wl0968 c4 = lw0 c4 (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wl0969 : Complete 4 → ⟪ (S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wl0969 c4 = lw0 c4 (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wl0970 : Complete 4 → ⟪ (K3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wl0970 c4 = lw0 c4 (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wl0971 : Complete 4 → ⟪ (CX14 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0971 c4 = lw0 c4 (CX14 ∷ CX14 ∷ []) [] tt tt Eq.refl

wl0972 : Complete 4 → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ []) ⟫ʷ
wl0972 c4 = lw0 c4 (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) (CX43 ∷ []) tt tt Eq.refl

wl0973 : Complete 4 → ⟪ (CX34 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
wl0973 c4 = lw0 c4 (CX34 ∷ []) (Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ []) tt tt Eq.refl

wl0974 : Complete 4 → ⟪ (CX34 ∷ CX43 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ []) ⟫ʷ
wl0974 c4 = lw0 c4 (CX34 ∷ CX43 ∷ CX34 ∷ []) (Sw34 ∷ []) tt tt Eq.refl
