------------------------------------------------------------------------
-- Presentations of groups
--
-- This module provides the definitions for the gates used in our
-- various sets of generators for Clifford+CS operators, and some
-- convenient abbreviations.
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Word.Base
open import Presentation.Tactics.Judgement

module Examples.Groups.Clifford+CS-3qubit.Gate where

data Gate : Set where

  -- Permutation generators.
  CCX0-gen : Gate
  CCX1-gen : Gate
  CCX2-gen : Gate
  CX01-gen : Gate
  CX10-gen : Gate
  CX12-gen : Gate
  CX21-gen : Gate
  CX02-gen : Gate
  CX20-gen : Gate
  X0-gen : Gate
  X1-gen : Gate
  X2-gen : Gate
  Swap01-gen : Gate
  Swap12-gen : Gate

  -- Diagonal generators.
  S0-gen : Gate
  S1-gen : Gate
  S2-gen : Gate
  CS01-gen : Gate
  CS12-gen : Gate
  CS02-gen : Gate
  CCZ-gen : Gate
  iI-gen : Gate

  -- K, CK, CCK' generators.
  CCK'-gen : Gate
  CK10-gen : Gate
  CK20-gen : Gate
  K0-gen : Gate

  -- ¬ used in Step0, Step3, (Step4?)
  K1-gen : Gate
  K2-gen : Gate

-- Abbreviations.
CCX0 : Word Gate
CCX0 = [ CCX0-gen ]ʷ

CCX1 : Word Gate
CCX1 = [ CCX1-gen ]ʷ

CCX2 : Word Gate
CCX2 = [ CCX2-gen ]ʷ

CX01 : Word Gate
CX01 = [ CX01-gen ]ʷ

CX10 : Word Gate
CX10 = [ CX10-gen ]ʷ

CX12 : Word Gate
CX12 = [ CX12-gen ]ʷ

CX21 : Word Gate
CX21 = [ CX21-gen ]ʷ

CX02 : Word Gate
CX02 = [ CX02-gen ]ʷ

CX20 : Word Gate
CX20 = [ CX20-gen ]ʷ

X0 : Word Gate
X0 = [ X0-gen ]ʷ

X1 : Word Gate
X1 = [ X1-gen ]ʷ

X2 : Word Gate
X2 = [ X2-gen ]ʷ

Swap01 : Word Gate
Swap01 = [ Swap01-gen ]ʷ

Swap12 : Word Gate
Swap12 = [ Swap12-gen ]ʷ

S0 : Word Gate
S0 = [ S0-gen ]ʷ

S1 : Word Gate
S1 = [ S1-gen ]ʷ

S2 : Word Gate
S2 = [ S2-gen ]ʷ

CS01 : Word Gate
CS01 = [ CS01-gen ]ʷ

CS12 : Word Gate
CS12 = [ CS12-gen ]ʷ

CS02 : Word Gate
CS02 = [ CS02-gen ]ʷ

CCZ : Word Gate
CCZ = [ CCZ-gen ]ʷ

iI : Word Gate
iI = [ iI-gen ]ʷ

CCK' : Word Gate
CCK' = [ CCK'-gen ]ʷ

CK10 : Word Gate
CK10 = [ CK10-gen ]ʷ

CK20 : Word Gate
CK20 = [ CK20-gen ]ʷ

K0 : Word Gate
K0 = [ K0-gen ]ʷ

K1 : Word Gate
K1 = [ K1-gen ]ʷ

K2 : Word Gate
K2 = [ K2-gen ]ʷ

