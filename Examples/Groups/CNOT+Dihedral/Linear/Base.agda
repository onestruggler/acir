------------------------------------------------------------------------
-- Presentations of groups
--
-- The linear coset tower: CNOT and SWAP circuits and their coset
-- representatives
--
-- A linear circuit — CNOTs and SWAPs only — denotes an invertible
-- matrix over F₂.  On ₁₊ n wires, every such matrix g factors as
--
--     g = h ↑ · s u · r ℓ                 (operator order: r ℓ first)
--
-- where h acts on the top n wires, ℓ is the row 0 of g (the parity
-- that g writes on wire 0), and u is the column of g ∘ (r ℓ)⁻¹ mapped
-- to wire 0 (with u₀ = 1).  The representatives r and s are built one
-- wire at a time, a gadget on the bottom wires followed by the
-- representative one wire up, so that a generator acting on the upper
-- wires passes through by the step one level down, and a generator on
-- the bottom wires meets only the gadget (Linear.Local).
--
--   NZ n          nonzero vectors in F₂ⁿ, built from the bottom wire:
--                 e₀ = (1,0,…,0), cx v = (1 ∷ v), sw v = (0 ∷ v)
--   r ℓ           a circuit whose output wire 0 carries the parity ℓ·x
--   s u           a circuit sending the basis vector u to e₀
--   KLet / K'Let  the letters of the stabilisers of the row e₀ and of
--                 the column e₀ that the steps emit
--
-- This module holds the definitions only; Linear.Steps proves the
-- step lemmas.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Linear.Base where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Linear.Local using (CX01)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Linear generators

data LGen : ℕ → Set where
  cnot swap : LGen (₂₊ n)
  _↥ₗ       : LGen n → LGen (₁₊ n)

ι : LGen n → Gen n
ι cnot     = CNOT-gen
ι swap     = SWAP-gen
ι (g ↥ₗ)   = ι g ↥

-- A linear word as a circuit.
⌊_⌋ : Word (LGen n) → Circuit n
⌊ [ g ]ʷ ⌋ = [ ι g ]ʷ
⌊ ε ⌋      = ε
⌊ w • v ⌋  = ⌊ w ⌋ • ⌊ v ⌋

------------------------------------------------------------------------
-- Nonzero vectors

data NZ : ℕ → Set where
  e₀    : NZ (₁₊ n)
  cx sw : NZ (₁₊ n) → NZ (₂₊ n)

vec : NZ n → Vec Bool n
vec {₁₊ n} e₀ = true ∷ replicate n false
vec (cx v)    = true ∷ vec v
vec (sw v)    = false ∷ vec v

------------------------------------------------------------------------
-- The representatives

-- The parity ℓ·x on wire 0.
r : NZ n → Circuit n
r e₀     = ε
r (cx ℓ) = CNOT • r ℓ ↑
r (sw ℓ) = SWAP • r ℓ ↑

-- The vector u to e₀.
s : NZ n → Circuit n
s e₀     = ε
s (cx u) = CX01 • s u ↑
s (sw u) = SWAP • s u ↑

-- The vectors with u₀ = 1, the ones the normal form uses.
data SOne : ℕ → Set where
  one₀ : SOne (₁₊ n)
  one  : NZ (₁₊ n) → SOne (₂₊ n)

s₁ : SOne n → Circuit n
s₁ one₀    = ε
s₁ (one u) = CX01 • s u ↑

------------------------------------------------------------------------
-- How the generators act on the data

-- Rows: ℓ ↦ ℓ ∘ y.
infixl 5 _⋆_
_⋆_ : NZ n → LGen n → NZ n
e₀        ⋆ (y ↥ₗ) = e₀
cx ℓ      ⋆ (y ↥ₗ) = cx (ℓ ⋆ y)
sw ℓ      ⋆ (y ↥ₗ) = sw (ℓ ⋆ y)
e₀        ⋆ cnot   = cx e₀
e₀        ⋆ swap   = sw e₀
cx e₀     ⋆ cnot   = e₀
cx e₀     ⋆ swap   = cx e₀
sw e₀     ⋆ cnot   = sw e₀
sw e₀     ⋆ swap   = e₀
cx (cx ℓ) ⋆ cnot   = cx (sw ℓ)
cx (cx ℓ) ⋆ swap   = cx (cx ℓ)
cx (sw ℓ) ⋆ cnot   = cx (cx ℓ)
cx (sw ℓ) ⋆ swap   = sw (cx ℓ)
sw (cx ℓ) ⋆ cnot   = sw (cx ℓ)
sw (cx ℓ) ⋆ swap   = cx (sw ℓ)
sw (sw ℓ) ⋆ cnot   = sw (sw ℓ)
sw (sw ℓ) ⋆ swap   = sw (sw ℓ)

-- Columns: u ↦ y⁻¹ u (= y u, the generators being involutions).
infixl 5 _⋆'_
_⋆'_ : NZ n → LGen n → NZ n
e₀        ⋆' (y ↥ₗ) = e₀
cx u      ⋆' (y ↥ₗ) = cx (u ⋆' y)
sw u      ⋆' (y ↥ₗ) = sw (u ⋆' y)
e₀        ⋆' cnot   = e₀
e₀        ⋆' swap   = sw e₀
cx e₀     ⋆' cnot   = sw e₀
cx e₀     ⋆' swap   = cx e₀
sw e₀     ⋆' cnot   = cx e₀
sw e₀     ⋆' swap   = e₀
cx (cx u) ⋆' cnot   = sw (cx u)
cx (cx u) ⋆' swap   = cx (cx u)
cx (sw u) ⋆' cnot   = cx (sw u)
cx (sw u) ⋆' swap   = sw (cx u)
sw (cx u) ⋆' cnot   = cx (cx u)
sw (cx u) ⋆' swap   = cx (sw u)
sw (sw u) ⋆' cnot   = sw (sw u)
sw (sw u) ⋆' swap   = sw (sw u)

------------------------------------------------------------------------
-- The letters the steps emit

-- The stabiliser of the row e₀: generators above wire 0, and CX01.
data KLet : ℕ → Set where
  kup : LGen n → KLet (₁₊ n)
  kcx : KLet (₂₊ n)

κ : KLet n → Circuit n
κ (kup y) = [ ι y ↥ ]ʷ
κ kcx     = CX01

⟪_⟫ : Word (KLet n) → Circuit n
⟪ [ k ]ʷ ⟫ = κ k
⟪ ε ⟫      = ε
⟪ w • v ⟫  = ⟪ w ⟫ • ⟪ v ⟫

-- The stabiliser of the column e₀: generators above wire 0, and CNOT.
data K'Let : ℕ → Set where
  kup'  : LGen n → K'Let (₁₊ n)
  kcnot : K'Let (₂₊ n)

κ' : K'Let n → Circuit n
κ' (kup' y) = [ ι y ↥ ]ʷ
κ' kcnot    = CNOT

⟪_⟫' : Word (K'Let n) → Circuit n
⟪ [ k ]ʷ ⟫' = κ' k
⟪ ε ⟫'      = ε
⟪ w • v ⟫'  = ⟪ w ⟫' • ⟪ v ⟫'

-- Letters of the level below, carried past a gadget.
lift-cx lift-sw : Word (KLet (₁₊ n)) → Word (KLet (₂₊ n))
lift-cx [ kup y ]ʷ = [ kup (y ↥ₗ) ]ʷ
lift-cx [ kcx ]ʷ   = [ kup swap ]ʷ • [ kup cnot ]ʷ • [ kup swap ]ʷ
lift-cx ε          = ε
lift-cx (w • v)    = lift-cx w • lift-cx v
lift-sw [ kup y ]ʷ = [ kup (y ↥ₗ) ]ʷ
lift-sw [ kcx ]ʷ   = [ kup swap ]ʷ • [ kcx ]ʷ • [ kup swap ]ʷ
lift-sw ε          = ε
lift-sw (w • v)    = lift-sw w • lift-sw v

lift'-cx lift'-sw : Word (K'Let (₁₊ n)) → Word (K'Let (₂₊ n))
lift'-cx [ kup' y ]ʷ = [ kup' (y ↥ₗ) ]ʷ
lift'-cx [ kcnot ]ʷ  = [ kup' cnot ]ʷ
lift'-cx ε           = ε
lift'-cx (w • v)     = lift'-cx w • lift'-cx v
lift'-sw [ kup' y ]ʷ = [ kup' (y ↥ₗ) ]ʷ
lift'-sw [ kcnot ]ʷ  = [ kup' swap ]ʷ • [ kcnot ]ʷ • [ kup' swap ]ʷ
lift'-sw ε           = ε
lift'-sw (w • v)     = lift'-sw w • lift'-sw v

------------------------------------------------------------------------
-- The step outputs

-- r ℓ • y ≈ ⟪ rk ℓ y ⟫ • r (ℓ ⋆ y).
rk : NZ n → LGen n → Word (KLet n)
rk e₀        (y ↥ₗ) = [ kup y ]ʷ
rk (cx ℓ)    (y ↥ₗ) = lift-cx (rk ℓ y)
rk (sw ℓ)    (y ↥ₗ) = lift-sw (rk ℓ y)
rk e₀        cnot   = ε
rk e₀        swap   = ε
rk (cx e₀)   cnot   = ε
rk (cx e₀)   swap   = [ kcx ]ʷ
rk (sw e₀)   cnot   = [ kcx ]ʷ
rk (sw e₀)   swap   = ε
rk (cx (cx ℓ)) cnot = [ kup cnot ]ʷ • [ kup swap ]ʷ
rk (cx (cx ℓ)) swap = [ kup cnot ]ʷ • [ kcx ]ʷ
rk (cx (sw ℓ)) cnot = [ kup swap ]ʷ • [ kup cnot ]ʷ
rk (cx (sw ℓ)) swap = [ kup swap ]ʷ
rk (sw (cx ℓ)) cnot = [ kup cnot ]ʷ • [ kcx ]ʷ
rk (sw (cx ℓ)) swap = [ kup swap ]ʷ
rk (sw (sw ℓ)) cnot = [ kup cnot ]ʷ
rk (sw (sw ℓ)) swap = [ kup swap ]ʷ

-- s u • y ≈ ⟪ sk u y ⟫' • s (u ⋆' y).
sk : NZ n → LGen n → Word (K'Let n)
sk e₀        (y ↥ₗ) = [ kup' y ]ʷ
sk (cx u)    (y ↥ₗ) = lift'-cx (sk u y)
sk (sw u)    (y ↥ₗ) = lift'-sw (sk u y)
sk e₀        cnot   = [ kcnot ]ʷ
sk e₀        swap   = ε
sk (cx e₀)   cnot   = [ kcnot ]ʷ
sk (cx e₀)   swap   = [ kcnot ]ʷ
sk (sw e₀)   cnot   = [ kcnot ]ʷ
sk (sw e₀)   swap   = ε
sk (cx (cx u)) cnot = [ kcnot ]ʷ
sk (cx (cx u)) swap = [ kup' cnot ]ʷ • [ kup' swap ]ʷ • [ kup' cnot ]ʷ • [ kcnot ]ʷ
sk (cx (sw u)) cnot = [ kcnot ]ʷ • [ kup' cnot ]ʷ • [ kcnot ]ʷ
sk (cx (sw u)) swap = [ kup' swap ]ʷ
sk (sw (cx u)) cnot = [ kcnot ]ʷ
sk (sw (cx u)) swap = [ kup' swap ]ʷ
sk (sw (sw u)) cnot = [ kup' cnot ]ʷ
sk (sw (sw u)) swap = [ kup' swap ]ʷ

-- The normal form's column part absorbs a letter of the row's
-- stabiliser: s₁ u • κ k ≈ (nw u k) ↑ • s₁ (u ⋆ₙ k).
infixl 5 _⋆ₙ_
_⋆ₙ_ : SOne n → KLet n → SOne n
one₀     ⋆ₙ kup y = one₀
one u    ⋆ₙ kup y = one (u ⋆' y)
one₀     ⋆ₙ kcx   = one e₀
one e₀   ⋆ₙ kcx   = one₀
one (cx u) ⋆ₙ kcx = one (sw u)
one (sw u) ⋆ₙ kcx = one (cx u)

nw : SOne (₁₊ n) → KLet (₁₊ n) → Circuit n
nw one₀       (kup y) = [ ι y ]ʷ
nw (one u)    (kup y) = ⟪ sk u y ⟫'
nw one₀       kcx     = ε
nw (one e₀)   kcx     = ε
nw (one (cx u)) kcx   = SWAP • CNOT
nw (one (sw u)) kcx   = CNOT • SWAP

-- A word of such letters.
push : SOne (₁₊ n) → Word (KLet (₁₊ n)) → Circuit n × SOne (₁₊ n)
push u [ k ]ʷ  = nw u k , u ⋆ₙ k
push u ε       = ε , u
push u (w • v) =
  proj₁ (push u w) • proj₁ (push (proj₂ (push u w)) v) ,
  proj₂ (push (proj₂ (push u w)) v)
