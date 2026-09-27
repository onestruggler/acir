------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)

open import Examples.Groups.Clifford+CS-3qubit.Index
open import Examples.Groups.Clifford+CS-3qubit.Gate

module Examples.Groups.Clifford+CS-3qubit.MaybeEq-Instances where

instance
  MaybeEq-Index : MaybeEq Index
  MaybeEq-Index = record { _=m?_ = λ {
    ₀ ₀ → just Eq.refl ;
    ₁ ₁ → just Eq.refl ;
    ₂ ₂ → just Eq.refl ;
    ₃ ₃ → just Eq.refl ;
    ₄ ₄ → just Eq.refl ;
    ₅ ₅ → just Eq.refl ;
    ₆ ₆ → just Eq.refl ;
    ₇ ₇ → just Eq.refl;
    _ _ -> nothing}}

_=G?=_ : (x y : Gate) -> Maybe (x ≡ y)
CCX0-gen =G?= CCX0-gen = just Eq.refl
CCX1-gen =G?= CCX1-gen = just Eq.refl
CCX2-gen =G?= CCX2-gen = just Eq.refl
CX01-gen =G?= CX01-gen = just Eq.refl
CX10-gen =G?= CX10-gen = just Eq.refl
CX12-gen =G?= CX12-gen = just Eq.refl
CX21-gen =G?= CX21-gen = just Eq.refl
CX02-gen =G?= CX02-gen = just Eq.refl
CX20-gen =G?= CX20-gen = just Eq.refl
X0-gen =G?= X0-gen = just Eq.refl
X1-gen =G?= X1-gen = just Eq.refl
X2-gen =G?= X2-gen = just Eq.refl
Swap01-gen =G?= Swap01-gen = just Eq.refl
Swap12-gen =G?= Swap12-gen = just Eq.refl
S0-gen =G?= S0-gen = just Eq.refl
S1-gen =G?= S1-gen = just Eq.refl
S2-gen =G?= S2-gen = just Eq.refl
CS01-gen =G?= CS01-gen = just Eq.refl
CS12-gen =G?= CS12-gen = just Eq.refl
CS02-gen =G?= CS02-gen = just Eq.refl
CCZ-gen =G?= CCZ-gen = just Eq.refl
iI-gen =G?= iI-gen = just Eq.refl
CCK'-gen =G?= CCK'-gen = just Eq.refl
CK10-gen =G?= CK10-gen = just Eq.refl
CK20-gen =G?= CK20-gen = just Eq.refl
K0-gen =G?= K0-gen = just Eq.refl
_ =G?= _ = nothing

instance 
  MaybeEq-Gate : MaybeEq Gate
  MaybeEq-Gate ._=m?_ = _=G?=_ 


