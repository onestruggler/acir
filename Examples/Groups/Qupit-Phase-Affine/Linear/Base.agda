------------------------------------------------------------------------
-- Presentations of groups
--
-- The linear coset tower: linear circuits, rows and columns, and their
-- representatives
--
-- A linear circuit — controlled additions, multipliers and swaps —
-- denotes an invertible matrix over F_p.  On ₁₊ n wires every such
-- matrix g factors as
--
--     g = h ↑ · col v · r ℓ                (operator order: r ℓ first)
--
-- where ℓ is row 0 of g (the linear form g writes on wire 0), h acts
-- on the upper n wires, and col v adds multiples of wire 0 to them.
--
--   R w        the fan-in x₀ += w · (x₁, …, xₙ)
--   col v      the fan-out xᵢ += vᵢ x₀
--   NZ n       the nonzero rows: big a w = (a, w) with a ≠ 0, and
--              small ℓ = (0, ℓ)
--   r ℓ        a circuit with row 0 equal to ℓ: R w • M_a for big
--              rows, and SWAP followed by the representative one wire
--              up for small ones
--   KLet       letters of the stabiliser of the row (1, 0, …, 0): a
--              word on the upper wires, or the reversed addition
--              x₁ += c x₀
--
-- A generator y acts on rows (ℓ ⋆ y) and on the vectors of R and col
-- (⋆ᴿ, ⋆ᶜ); rk ℓ y is the stabiliser word the step emits, and push
-- carries a word of stabiliser letters across the column part.  The
-- step lemmas are Linear.Steps; the identities they rest on are
-- Linear.Fan.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Linear.Base
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; wmap)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; 0F ; 1F ; _+_ ; _*_ ; -_ ; _⁻¹ᶠ ; _⁻¹* ; _⊛_ ; -1*)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Linear generators

data LGen : ℕ → Set where
  cx sw : LGen (₂₊ n)
  mul   : F* → LGen (₁₊ n)
  _↥ₗ   : LGen n → LGen (₁₊ n)

ι : LGen n → Gen n
ι cx      = gate₂ CX-gate
ι sw      = gate₂ SWAP-gate
ι (mul a) = gate₁ (M-gate (proj₁ a) (proj₂ a))
ι (y ↥ₗ)  = ι y ↥

-- A linear word as a circuit.
⌊_⌋ : Word (LGen n) → Circuit n
⌊ [ y ]ʷ ⌋ = [ ι y ]ʷ
⌊ ε ⌋      = ε
⌊ w • v ⌋  = ⌊ w ⌋ • ⌊ v ⌋

-- A linear word one wire up.
_↑ₗ : Word (LGen n) → Word (LGen (₁₊ n))
_↑ₗ = wmap _↥ₗ

------------------------------------------------------------------------
-- Fan-in and fan-out

-- x₀ += w · (x₁, …, xₙ).
R : Vec F n → Circuit (₁₊ n)
R []      = ε
R (c ∷ w) = (SWAP • R w ↑ • SWAP) • CX ^ᶠ c

-- x₀ += w · (x₂, …, xₙ₊₁).
R₀ : Vec F n → Circuit (₂₊ n)
R₀ w = SWAP • R w ↑ • SWAP

-- xᵢ += vᵢ x₀.
col : Vec F n → Circuit (₁₊ n)
col []      = ε
col (c ∷ v) = (SWAP • col v ↑ • SWAP) • CXʳ ^ᶠ c

-- xᵢ₊₁ += vᵢ x₀.
C₀ : Vec F n → Circuit (₂₊ n)
C₀ v = SWAP • col v ↑ • SWAP

-- The fan-in as a linear word.
Rʷ : Vec F n → Word (LGen (₁₊ n))
Rʷ []      = ε
Rʷ (c ∷ w) = ([ sw ]ʷ • Rʷ w ↑ₗ • [ sw ]ʷ) • [ cx ]ʷ ^ toℕ c

-- The vector - c w.
negs : F → Vec F n → Vec F n
negs c = map (λ x → - (c * x))

------------------------------------------------------------------------
-- How a generator on the upper wires acts on the vectors

-- Fan-in coefficients: w ↦ w Y.
infixl 5 _⋆ᴿ_
_⋆ᴿ_ : Vec F n → LGen n → Vec F n
(c ∷ w)     ⋆ᴿ (y ↥ₗ) = c ∷ (w ⋆ᴿ y)
(c ∷ w)     ⋆ᴿ mul x  = c * proj₁ x ∷ w
(c ∷ d ∷ w) ⋆ᴿ cx     = c ∷ d + c ∷ w
(c ∷ d ∷ w) ⋆ᴿ sw     = d ∷ c ∷ w

-- Fan-out coefficients: v ↦ Y⁻¹ v.
infixl 5 _⋆ᶜ_
_⋆ᶜ_ : Vec F n → LGen n → Vec F n
(c ∷ v)     ⋆ᶜ (y ↥ₗ) = c ∷ (v ⋆ᶜ y)
(c ∷ v)     ⋆ᶜ mul x  = c * proj₁ (x ⁻¹*) ∷ v
(c ∷ d ∷ v) ⋆ᶜ cx     = - d + c ∷ d ∷ v
(c ∷ d ∷ v) ⋆ᶜ sw     = d ∷ c ∷ v

-- And a word of them.
infixl 5 _⋆ᶜ*_
_⋆ᶜ*_ : Vec F n → Word (LGen n) → Vec F n
v ⋆ᶜ* [ y ]ʷ  = v ⋆ᶜ y
v ⋆ᶜ* ε       = v
v ⋆ᶜ* (w • u) = v ⋆ᶜ* w ⋆ᶜ* u

------------------------------------------------------------------------
-- Rows and their representatives

data NZ : ℕ → Set where
  big   : F* → Vec F n → NZ (₁₊ n)
  small : NZ (₁₊ n) → NZ (₂₊ n)

-- The row itself.
row : NZ n → Vec F n
row (big a w) = proj₁ a ∷ w
row (small ℓ) = 0F ∷ row ℓ

r : NZ n → Circuit n
r (big a w) = R w • M⟨ a ⟩
r (small ℓ) = SWAP • r ℓ ↑

------------------------------------------------------------------------
-- The letters of the row stabiliser

data KLet : ℕ → Set where
  kup  : Word (LGen n) → KLet (₁₊ n)
  kcol : F → KLet (₂₊ n)

κ : KLet n → Circuit n
κ (kup L)  = ⌊ L ⌋ ↑
κ (kcol c) = CXʳ ^ᶠ c

⟪_⟫ : Word (KLet n) → Circuit n
⟪ [ k ]ʷ ⟫ = κ k
⟪ ε ⟫      = ε
⟪ w • v ⟫  = ⟪ w ⟫ • ⟪ v ⟫

-- Letters of the level below, past SWAP: x₂ += c x₁ becomes x₂ += c x₀.
lift-sw : Word (KLet (₁₊ n)) → Word (KLet (₂₊ n))
lift-sw [ kup L ]ʷ  = [ kup (L ↑ₗ) ]ʷ
lift-sw [ kcol c ]ʷ = [ kup [ sw ]ʷ ]ʷ • [ kcol c ]ʷ • [ kup [ sw ]ʷ ]ʷ
lift-sw ε           = ε
lift-sw (w • v)     = lift-sw w • lift-sw v

------------------------------------------------------------------------
-- The action on rows, and the letters it emits

-- A swap of a big row (a, c, w): the row (c, a, w), big if c ≠ 0.
big-sw : F* → (c : F) → Vec F n → Dec (c ≡ 0F) → NZ (₂₊ n)
big-sw a c w (yes _) = small (big a w)
big-sw a c w (no nc) = big (c , nc) (proj₁ a ∷ w)

big-sw-k : F* → (c : F) → Vec F n → Dec (c ≡ 0F) → Word (KLet (₂₊ n))
big-sw-k a c w (yes _) = ε
big-sw-k a c w (no nc) =
  [ kcol (c ⁻¹ᶠ) ]ʷ • [ kup (Rʷ (negs (c ⁻¹ᶠ) w)) ]ʷ • [ kup [ mul (a ⊛ (-1* ⊛ (c , nc) ⁻¹*)) ]ʷ ]ʷ

infixl 5 _⋆_
_⋆_ : NZ n → LGen n → NZ n
big a w         ⋆ (y ↥ₗ) = big a (w ⋆ᴿ y)
small ℓ         ⋆ (y ↥ₗ) = small (ℓ ⋆ y)
big a w         ⋆ mul x  = big (x ⊛ a) w
small ℓ         ⋆ mul x  = small ℓ
big a (c ∷ w)   ⋆ cx     = big a (c + proj₁ a ∷ w)
small ℓ         ⋆ cx     = small ℓ
big a (c ∷ w)   ⋆ sw     = big-sw a c w (c ≟ 0F)
small (big b w) ⋆ sw     = big b (0F ∷ w)
small (small ℓ) ⋆ sw     = small (small ℓ)

-- r ℓ • y ≈ ⟪ rk ℓ y ⟫ • r (ℓ ⋆ y).
rk : NZ n → LGen n → Word (KLet n)
rk (big a w)         (y ↥ₗ) = [ kup [ y ]ʷ ]ʷ
rk (small ℓ)         (y ↥ₗ) = lift-sw (rk ℓ y)
rk (big a w)         (mul x) = ε
rk (small ℓ)         (mul x) = [ kup [ mul x ]ʷ ]ʷ
rk (big a (c ∷ w))   cx     = ε
rk (small (big b w)) cx     =
  [ kcol (proj₁ b ⁻¹ᶠ) ]ʷ • [ kup (Rʷ (negs (proj₁ b ⁻¹ᶠ) w)) ]ʷ
rk (small (small ℓ)) cx     = [ kup [ cx ]ʷ ]ʷ
rk (big a (c ∷ w))   sw     = big-sw-k a c w (c ≟ 0F)
rk (small (big b w)) sw     = ε
rk (small (small ℓ)) sw     = [ kup [ sw ]ʷ ]ʷ

------------------------------------------------------------------------
-- The column part absorbs the letters

-- col v • κ k ≈ upk k ↑ • col (v ⋆ₖ k).
upk : KLet (₁₊ n) → Circuit n
upk (kup L)  = ⌊ L ⌋
upk (kcol c) = ε

infixl 5 _⋆ₖ_
_⋆ₖ_ : Vec F n → KLet (₁₊ n) → Vec F n
v       ⋆ₖ kup L  = v ⋆ᶜ* L
(d ∷ v) ⋆ₖ kcol c = d + c ∷ v

-- A word of letters.
push : Vec F n → Word (KLet (₁₊ n)) → Circuit n × Vec F n
push v [ k ]ʷ  = upk k , v ⋆ₖ k
push v ε       = ε , v
push v (w • u) =
  proj₁ (push v w) • proj₁ (push (proj₂ (push v w)) u) ,
  proj₂ (push (proj₂ (push v w)) u)
