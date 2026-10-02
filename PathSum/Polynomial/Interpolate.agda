------------------------------------------------------------------------
-- Presentations of groups
--
-- Every function on the Boolean cube is a multilinear polynomial
--
-- Section 2 of Amy's QPL 2018 paper takes for granted that Boolean
-- functions and multilinear polynomials correspond: a phase is any
-- function of the Boolean point, an output any Boolean function, each
-- written as a polynomial.  Uniqueness is PathSum.Mobius (values
-- determine coefficients, modulo any c; PathSum.Polynomial.Bind's
-- poly-ext and PathSum.Polynomial.Boolean's ≈-from-values).  This
-- module proves existence, by interpolation at the head variable:
--
--    P(x₀, x′) = P₀(x′) + x₀ (P₁(x′) − P₀(x′)),
--
-- P₀ and P₁ interpolating the function at x₀ = 0 and x₀ = 1 (interp,
-- evalˢ-interp).  So every F : (Fin n → Bool) → ℤ is the value of a
-- polynomial in n input variables (polyᶻ, eval-polyᶻ), unique
-- coefficient by coefficient (polyᶻ-unique); and every Boolean
-- function f is the reading modulo 2 of one (polyᴮ, the polynomial of
-- the bits [ f x ]ᶻ: odd-polyᴮ), Boolean-valued (BoolValued-polyᴮ) and
-- unique modulo 2 (polyᴮ-unique).
--
-- The functions must read their argument only through its values
-- (RespectsZ, RespectsB): assignments are functions, equal here only
-- pointwise, and without function extensionality nothing forces an
-- arbitrary F to give pointwise equal assignments the same value,
-- while a polynomial's value does (PathSum.Polynomial.Properties.
-- eval-cong).  Every function written in terms of the bits of its
-- argument -- in particular every polynomial's reading -- respects
-- them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Interpolate where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _+_; _-_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.AssignSum using (RespectsZ; _∷ᵃ_)
open import PathSum.HiddenShift.Walsh using (RespectsB)
open import PathSum.Mobius using (evalˢ; eval-nested)
open import PathSum.Polynomial using (Poly; eval; Σsub; sat; _≈[_]_)
open import PathSum.Polynomial.Bind using (odd; poly-ext)
open import PathSum.Polynomial.Boolean using
  (IsBit; BoolValued; IsBit-if; ≈-from-values)
open import PathSum.Polynomial.Parity using (odd-[]; odd-≡)
open import PathSum.Polynomial.Properties using (Σsub-0; Σsub-cong)

open +-*-Solver using (solve; _:+_; _:-_; _:=_)

private
  variable
    n k : ℕ


------------------------------------------------------------------------
-- Interpolation in one block of variables

-- The coefficients: at x₀ absent, those interpolating F at x₀ = 0; at
-- x₀ present, those interpolating the difference at x₀ = 1 and 0.

interp : ((Fin k → Bool) → ℤ) → Subset k → ℤ
interp {zero}  F []            = F (λ ())
interp {suc k} F (outside ∷ s) = interp (λ w → F (false ∷ᵃ w)) s
interp {suc k} F (inside  ∷ s) =
  interp (λ w → F (true ∷ᵃ w) - F (false ∷ᵃ w)) s

private
  -- Fixing the head bit keeps a function respectful.

  ∷ᵃ-cong : (b : Bool) {g h : Fin k → Bool} → (∀ j → g j ≡ h j) →
            ∀ j → (b ∷ᵃ g) j ≡ (b ∷ᵃ h) j
  ∷ᵃ-cong b g≗h zero    = refl
  ∷ᵃ-cong b g≗h (suc j) = g≗h j

  fix : {F : (Fin (suc k) → Bool) → ℤ} → RespectsZ F →
        ∀ b → RespectsZ (λ w → F (b ∷ᵃ w))
  fix resp b g h g≗h = resp (b ∷ᵃ g) (b ∷ᵃ h) (∷ᵃ-cong b g≗h)

  diff : {F : (Fin (suc k) → Bool) → ℤ} → RespectsZ F →
         RespectsZ (λ w → F (true ∷ᵃ w) - F (false ∷ᵃ w))
  diff resp g h g≗h = cong₂ _-_ (fix resp true g h g≗h)
                                (fix resp false g h g≗h)

  -- The part of the value with the head variable present.

  head-part : (g : Subset k → ℤ) (w : Fin k → Bool) → ∀ b →
              Σsub (λ s → if b ∧ sat s w then g s else 0ℤ) ≡
              (if b then evalˢ g w else 0ℤ)
  head-part {k} g w true  = refl
  head-part {k} g w false = Σsub-0 {k}

  rebuild : ∀ a b → (a - b) + b ≡ a
  rebuild = solve 2 (λ a b → (a :- b) :+ b := a) refl

-- The interpolating coefficients take the values of F.

evalˢ-interp : (F : (Fin k → Bool) → ℤ) → RespectsZ F →
               ∀ v → evalˢ (interp F) v ≡ F v
evalˢ-interp {zero}  F resp v = resp _ v (λ ())
evalˢ-interp {suc k} F resp v = go (v zero) refl
  where
  v′ : Fin k → Bool
  v′ j = v (suc j)

  F₀ F₁ : (Fin k → Bool) → ℤ
  F₀ w = F (false ∷ᵃ w)
  F₁ w = F (true ∷ᵃ w) - F (false ∷ᵃ w)

  split : ∀ b → v zero ≡ b →
          evalˢ (interp F) v ≡
          (if b then evalˢ (interp F₁) v′ else 0ℤ) + evalˢ (interp F₀) v′
  split b e = cong (_+ evalˢ (interp F₀) v′)
    (trans (cong (λ c → Σsub (λ s → if c ∧ sat s v′
                                    then interp F₁ s else 0ℤ)) e)
           (head-part (interp F₁) v′ b))

  -- v is b ∷ v′, pointwise.

  same-as : ∀ b → v zero ≡ b → ∀ j → (b ∷ᵃ v′) j ≡ v j
  same-as b e zero    = sym e
  same-as b e (suc j) = refl

  go : ∀ b → v zero ≡ b → evalˢ (interp F) v ≡ F v
  go false e = trans (split false e)
    (trans (+-identityˡ _)
    (trans (evalˢ-interp F₀ (fix resp false) v′)
           (resp (false ∷ᵃ v′) v (same-as false e))))
  go true  e = trans (split true e)
    (trans (cong₂ _+_ (evalˢ-interp F₁ (diff resp) v′)
                      (evalˢ-interp F₀ (fix resp false) v′))
    (trans (rebuild (F (true ∷ᵃ v′)) (F (false ∷ᵃ v′)))
           (resp (true ∷ᵃ v′) v (same-as true e))))


------------------------------------------------------------------------
-- Polynomials in the input variables

-- The multilinear polynomial of F: no path variables.

polyᶻ : ((Fin n → Bool) → ℤ) → Poly n 0
polyᶻ F γ = interp F (proj₁ γ)

-- It takes the values of F ...

eval-polyᶻ : (F : (Fin n → Bool) → ℤ) → RespectsZ F →
             ∀ x (y : Fin 0 → Bool) → eval (polyᶻ F) x y ≡ F x
eval-polyᶻ F resp x y =
  trans (eval-nested (polyᶻ F) x y) (evalˢ-interp F resp x)

-- ... and is the only polynomial that does.

polyᶻ-unique : (F : (Fin n → Bool) → ℤ) → RespectsZ F → (P : Poly n 0) →
               (∀ x (y : Fin 0 → Bool) → eval P x y ≡ F x) →
               ∀ γ → P γ ≡ polyᶻ F γ
polyᶻ-unique F resp P h = poly-ext P (polyᶻ F) λ x y →
  trans (h x y) (sym (eval-polyᶻ F resp x y))


------------------------------------------------------------------------
-- Boolean functions

-- The Boolean polynomial of f: the polynomial of its bits.

polyᴮ : ((Fin n → Bool) → Bool) → Poly n 0
polyᴮ f = polyᶻ (λ x → [ f x ]ᶻ)

private
  bits : (f : (Fin n → Bool) → Bool) → RespectsB f →
         RespectsZ (λ x → [ f x ]ᶻ)
  bits f resp g h g≗h = cong [_]ᶻ (resp g h g≗h)

eval-polyᴮ : (f : (Fin n → Bool) → Bool) → RespectsB f →
             ∀ x (y : Fin 0 → Bool) → eval (polyᴮ f) x y ≡ [ f x ]ᶻ
eval-polyᴮ f resp = eval-polyᶻ (λ x → [ f x ]ᶻ) (bits f resp)

-- Read modulo 2, as an output is, it is f ...

odd-polyᴮ : (f : (Fin n → Bool) → Bool) → RespectsB f →
            ∀ x (y : Fin 0 → Bool) → odd (eval (polyᴮ f) x y) ≡ f x
odd-polyᴮ f resp x y =
  trans (cong odd (eval-polyᴮ f resp x y)) (odd-[] (f x))

-- ... its values are bits ...

BoolValued-polyᴮ : (f : (Fin n → Bool) → Bool) → RespectsB f →
                   BoolValued (polyᴮ f)
BoolValued-polyᴮ f resp x y =
  subst IsBit (sym (eval-polyᴮ f resp x y)) (IsBit-if (f x))

-- ... and every polynomial whose reading is f agrees with it modulo 2,
-- coefficient by coefficient.

polyᴮ-unique : (f : (Fin n → Bool) → Bool) → RespectsB f → (P : Poly n 0) →
               (∀ x (y : Fin 0 → Bool) → odd (eval P x y) ≡ f x) →
               P ≈[ + 2 ] polyᴮ f
polyᴮ-unique f resp P h = ≈-from-values P (polyᴮ f) λ x y →
  odd-≡ (eval P x y) (eval (polyᴮ f) x y)
        (trans (h x y) (sym (odd-polyᴮ f resp x y)))
