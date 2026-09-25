------------------------------------------------------------------------
-- Presentations of groups
--
-- Parallel composition of path-sums (Amy, QPL 2018, section 2.1 and
-- remark 2.8)
--
-- Section 2.1 of the paper composes path-sums "vertically", on
-- distinct subsystems, "in the obvious way -- concatenating the inputs
-- and outputs then adding the phase polynomials with appropriate
-- renaming".  That is _⊗ᴾ_ of PathSum.Compose: ξ₁ on the first n₁
-- wires, with the first m₁ path variables, and ξ₂ on the last n₂ wires,
-- with the last m₂.  Beyond remark 2.8 the paper states nothing about
-- it; what it means is proved here.
--
-- On a pair of concatenated paths y₁ ++ y₂ from the input x₁ ++ x₂, the
-- phase of ξ₁ ⊗ ξ₂ is P₁(x₁,y₁) + P₂(x₂,y₂) (eval-⊗), its outputs are
-- f₁(x₁,y₁) ++ f₂(x₂,y₂) (outBit-⊗), so the path hits z₁ ++ z₂ exactly
-- when both halves hit theirs (hits-⊗).  Hence the entry of the
-- operator from x₁ x₂ to z₁ z₂ is the product of the two entries,
--
--    U_{ξ₁⊗ξ₂}(x₁x₂, z₁z₂) = U_ξ₁(x₁, z₁) · U_ξ₂(x₂, z₂),
--
-- that is, U_{ξ₁⊗ξ₂} = U_ξ₁ ⊗ U_ξ₂, exactly and unnormalised, because
-- the normalisations add (amp-⊗, and amp-⊗-blocks at states that are
-- not written as concatenations).  PathSum.Ring does not prove its
-- product ⊛ commutative, so the other order is stated as well
-- (amp-⊗′); both come from the rot forms amp-⊗ʳ and amp-⊗ʳ′, in which
-- one entry is written out as the sum of powers of ζ that it is.  So
-- _⊗ᴾ_ is well defined on path-sums up to ≋ (⊗ᴾ-cong).
--
-- Remark 2.8 says that path-sums identify circuits that are equal up
-- to the laws of symmetric monoidal categories, the bifunctoriality law
-- being its first example.  Here ⊗ is a bifunctor up to ≋: it
-- preserves identities (⊗ᴾ-idPS) and interchanges with sequential
-- composition,
--
--    (ξ₁ ⊗ ξ₂) ∘ (ζ₁ ⊗ ζ₂) ≋ (ξ₁ ∘ ζ₁) ⊗ (ξ₂ ∘ ζ₂)    (⊗-interchange),
--
-- whose amplitudes agree exactly (amp-interchange).  Both sides sum,
-- over paths of all four path-sums, the same powers of ζ; they only
-- list the path variables in different orders.  The law drawn in
-- remark 2.8 follows: ξ₁ on the upper wires and ξ₂ on the lower ones,
-- in either order, is ξ₁ ⊗ ξ₂ (⊗-sequential, ⊗-sequential′), so the
-- two orders are equivalent (remark-2-8).
--
-- Departures from the paper.  The remark says such circuits are
-- "strictly equal"; here they are equivalent (≋), not equal.  The two
-- sides of the interchange law have normalisations
-- (j₁ + j₂) + (k₁ + k₂) and (j₁ + k₁) + (j₂ + k₂), equal only
-- propositionally, and likewise their numbers of path variables; the
-- path variables come in different orders; and polynomials are
-- functions, which --safe without function extensionality does not
-- identify from pointwise equality.  Equality up to a reordering of
-- path variables is not formalised.  The remark's other example, the
-- naturality of SWAP, is PathSum.Compose.Swap.  Of the remaining laws
-- of a monoidal category only the left unit law is stated
-- (⊗ᴾ-identityˡ, with idPS on no wires): associativity and the right
-- unit law relate path-sums on (n₁ + n₂) + n₃ and n₁ + (n₂ + n₃)
-- wires, or on n + 0 and n wires, which are equal only
-- propositionally, and ≋ relates path-sums on the same wires.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Tensor (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Bool.Properties using (∧-assoc)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Integer.Base using (ℤ; _+_)
open import Data.Integer.Properties using (+-comm; +-identityˡ)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Sum.Base using ([_,_]′)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using (same; _=ᵇ_; same-≗)
open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.Compose using (⊗ˡ; ⊗ʳ; _⊗ᴾ_; _∘ᴾ_)
open import PathSum.Compose.Gates M₀ using (≋-amp; amp-ext)
open import PathSum.Compose.Laws M₀ using (∘ᴾ-identityˡ; ∘ᴾ-identityʳ)
open import PathSum.Compose.Matrix M₀ using (amp-⊛)
open import PathSum.Compose.Properties M₀ using
  (eval-∘; hits-∘; hits-same; amp-≗ˣ; prop-2-7ʳ)
open import PathSum.Compose.Sum M₀ using
  (_++ᵃ_; ++ᵃ-↑ˡ; ++ᵃ-↑ʳ; ++ᵃ-split; Σᴮ-++; Σᴮ-swap; rot-comm; scale-+;
   scale-exp; scale-rot; scale-Σᴮ; if-cong; zpow-≡; rot-guard; rot-if;
   if-Σᴮ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; Σᴮ; Σᴮ-cong; zpow; rot; rot-map; rot-exp; rot-comp;
   rot-zpow; rot-0ᴬ; rot-Σᴮ; √2·-map; √2·-0ᴬ; scale; scale-map)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; _≋_; ≋-sym; ≋-trans; amp-≗; outBit-μ;
   eval-0ᴾ-val)
open import PathSum.Polynomial using (x[_]; eval)
open import PathSum.Polynomial.Bind using (rename; eval-rename; odd)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-cong)
open import PathSum.Ring M₀ using (_⊛_)

private
  variable
    n n₁ n₂ k k′ k₁ k₂ j j′ j₁ j₂ l l′ l₁ l₂ m m′ m₁ m₂ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The two blocks of an assignment

-- An assignment to n₁ + n₂ wires, read on the first n₁ (the wires of
-- the upper path-sum) and on the last n₂ (those of the lower one).

takeᵃ : ∀ n₂ → Assign (n₁ ℕ+ n₂) → Assign n₁
takeᵃ n₂ x i = x (i ↑ˡ n₂)

dropᵃ : ∀ n₁ → Assign (n₁ ℕ+ n₂) → Assign n₂
dropᵃ n₁ x i = x (n₁ ↑ʳ i)

-- Every index of n₁ + n₂ is in one of the two blocks.

by-blocks : ∀ n₁ n₂ {P : Fin (n₁ ℕ+ n₂) → Set} →
            (∀ i → P (i ↑ˡ n₂)) → (∀ i → P (n₁ ↑ʳ i)) → ∀ w → P w
by-blocks zero     n₂     l r w       = r w
by-blocks (suc n₁) n₂     l r zero    = l zero
by-blocks (suc n₁) n₂ {P} l r (suc w) =
  by-blocks n₁ n₂ {λ w′ → P (suc w′)} (λ i → l (suc i)) r w

-- Two concatenations agree when both blocks do.

same-++ : (a : Assign k) (b : Assign l) (c : Assign k) (d : Assign l) →
          same (a ++ᵃ b) (c ++ᵃ d) ≡ same a c ∧ same b d
same-++ {zero}  a b c d = refl
same-++ {suc k} a b c d = trans
  (cong ((a zero =ᵇ c zero) ∧_)
        (same-++ (λ i → a (suc i)) b (λ i → c (suc i)) d))
  (sym (∧-assoc (a zero =ᵇ c zero)
                (same (λ i → a (suc i)) (λ i → c (suc i))) (same b d)))


------------------------------------------------------------------------
-- The phase and the outputs of a tensor

-- The outputs on the upper wires are ξ₁'s, renamed, and those on the
-- lower wires ξ₂'s.

out-⊗ˡ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) (i : Fin n₁) →
         out (ξ₁ ⊗ᴾ ξ₂) (i ↑ˡ n₂) ≡ rename (⊗ˡ n₂ m₂) (out ξ₁ i)
out-⊗ˡ {n₁ = n₁} {m₁ = m₁} {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ i =
  cong [ (λ i′ → rename (⊗ˡ n₂ m₂) (out ξ₁ i′))
       , (λ i′ → rename (⊗ʳ n₁ m₁) (out ξ₂ i′)) ]′
       (splitAt-↑ˡ n₁ i n₂)

out-⊗ʳ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) (i : Fin n₂) →
         out (ξ₁ ⊗ᴾ ξ₂) (n₁ ↑ʳ i) ≡ rename (⊗ʳ n₁ m₁) (out ξ₂ i)
out-⊗ʳ {n₁ = n₁} {m₁ = m₁} {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ i =
  cong [ (λ i′ → rename (⊗ˡ n₂ m₂) (out ξ₁ i′))
       , (λ i′ → rename (⊗ʳ n₁ m₁) (out ξ₂ i′)) ]′
       (splitAt-↑ʳ n₁ n₂ i)

-- At any assignment, the phase is ξ₁'s at the first blocks plus ξ₂'s
-- at the second, and each output is its own path-sum's there.

eval-⊗-blocks : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) →
                eval (phase (ξ₁ ⊗ᴾ ξ₂)) x y ≡
                eval (phase ξ₁) (takeᵃ n₂ x) (takeᵃ m₂ y) +
                eval (phase ξ₂) (dropᵃ n₁ x) (dropᵃ m₁ y)
eval-⊗-blocks {n₁ = n₁} {m₁ = m₁} {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ x y = trans
  (eval-+ᴾ (rename (⊗ˡ n₂ m₂) (phase ξ₁)) (rename (⊗ʳ n₁ m₁) (phase ξ₂))
           x y)
  (cong₂ _+_ (eval-rename (⊗ˡ n₂ m₂) (phase ξ₁) x y)
             (eval-rename (⊗ʳ n₁ m₁) (phase ξ₂) x y))

outBit-⊗ˡ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
            (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) (i : Fin n₁) →
            outBit (ξ₁ ⊗ᴾ ξ₂) x y (i ↑ˡ n₂) ≡
            outBit ξ₁ (takeᵃ n₂ x) (takeᵃ m₂ y) i
outBit-⊗ˡ {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ x y i = trans
  (cong (λ P → odd (eval P x y)) (out-⊗ˡ ξ₁ ξ₂ i))
  (cong odd (eval-rename (⊗ˡ n₂ m₂) (out ξ₁ i) x y))

outBit-⊗ʳ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
            (x : Assign (n₁ ℕ+ n₂)) (y : Assign (m₁ ℕ+ m₂)) (i : Fin n₂) →
            outBit (ξ₁ ⊗ᴾ ξ₂) x y (n₁ ↑ʳ i) ≡
            outBit ξ₂ (dropᵃ n₁ x) (dropᵃ m₁ y) i
outBit-⊗ʳ {n₁ = n₁} {m₁ = m₁} ξ₁ ξ₂ x y i = trans
  (cong (λ P → odd (eval P x y)) (out-⊗ʳ ξ₁ ξ₂ i))
  (cong odd (eval-rename (⊗ʳ n₁ m₁) (out ξ₂ i) x y))

private
  outBit-≗ : (ξ : PathSum n k m) {x x′ : Assign n} {y y′ : Assign m} →
             (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
             ∀ w → outBit ξ x y w ≡ outBit ξ x′ y′ w
  outBit-≗ ξ x≗x′ y≗y′ w = cong odd (eval-cong (out ξ w) x≗x′ y≗y′)

-- On concatenated inputs and paths: the phase is the sum of the two
-- phases ...

eval-⊗ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
         (x₁ : Assign n₁) (x₂ : Assign n₂)
         (y₁ : Assign m₁) (y₂ : Assign m₂) →
         eval (phase (ξ₁ ⊗ᴾ ξ₂)) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) ≡
         eval (phase ξ₁) x₁ y₁ + eval (phase ξ₂) x₂ y₂
eval-⊗ {n₁ = n₁} {m₁ = m₁} {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ x₁ x₂ y₁ y₂ = trans
  (eval-⊗-blocks ξ₁ ξ₂ (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂))
  (cong₂ _+_
    (eval-cong (phase ξ₁) {x = takeᵃ n₂ (x₁ ++ᵃ x₂)} {x′ = x₁}
               {y = takeᵃ m₂ (y₁ ++ᵃ y₂)} {y′ = y₁}
               (++ᵃ-↑ˡ x₁ x₂) (++ᵃ-↑ˡ y₁ y₂))
    (eval-cong (phase ξ₂) {x = dropᵃ n₁ (x₁ ++ᵃ x₂)} {x′ = x₂}
               {y = dropᵃ m₁ (y₁ ++ᵃ y₂)} {y′ = y₂}
               (++ᵃ-↑ʳ x₁ x₂) (++ᵃ-↑ʳ y₁ y₂)))

-- ... the outputs are the concatenation of the two outputs ...

outBit-⊗ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
           (x₁ : Assign n₁) (x₂ : Assign n₂)
           (y₁ : Assign m₁) (y₂ : Assign m₂) (w : Fin (n₁ ℕ+ n₂)) →
           outBit (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) w ≡
           (outBit ξ₁ x₁ y₁ ++ᵃ outBit ξ₂ x₂ y₂) w
outBit-⊗ {n₁ = n₁} {n₂ = n₂} ξ₁ ξ₂ x₁ x₂ y₁ y₂ =
  by-blocks n₁ n₂ upper lower
  where
  upper : ∀ i → outBit (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) (i ↑ˡ n₂) ≡
                (outBit ξ₁ x₁ y₁ ++ᵃ outBit ξ₂ x₂ y₂) (i ↑ˡ n₂)
  upper i = trans (outBit-⊗ˡ ξ₁ ξ₂ (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) i)
    (trans (outBit-≗ ξ₁ (++ᵃ-↑ˡ x₁ x₂) (++ᵃ-↑ˡ y₁ y₂) i)
           (sym (++ᵃ-↑ˡ (outBit ξ₁ x₁ y₁) (outBit ξ₂ x₂ y₂) i)))

  lower : ∀ i → outBit (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) (n₁ ↑ʳ i) ≡
                (outBit ξ₁ x₁ y₁ ++ᵃ outBit ξ₂ x₂ y₂) (n₁ ↑ʳ i)
  lower i = trans (outBit-⊗ʳ ξ₁ ξ₂ (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) i)
    (trans (outBit-≗ ξ₂ (++ᵃ-↑ʳ x₁ x₂) (++ᵃ-↑ʳ y₁ y₂) i)
           (sym (++ᵃ-↑ʳ (outBit ξ₁ x₁ y₁) (outBit ξ₂ x₂ y₂) i)))

-- ... and the path hits a concatenated state when both halves hit
-- theirs.

hits-⊗ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
         (x₁ z₁ : Assign n₁) (x₂ z₂ : Assign n₂)
         (y₁ : Assign m₁) (y₂ : Assign m₂) →
         hits (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) (z₁ ++ᵃ z₂) ≡
         hits ξ₁ x₁ y₁ z₁ ∧ hits ξ₂ x₂ y₂ z₂
hits-⊗ ξ₁ ξ₂ x₁ z₁ x₂ z₂ y₁ y₂ = trans
  (hits-same (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) (z₁ ++ᵃ z₂))
  (trans (same-≗ {x = outBit (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂)}
                 {x′ = outBit ξ₁ x₁ y₁ ++ᵃ outBit ξ₂ x₂ y₂}
                 {z = z₁ ++ᵃ z₂} {z′ = z₁ ++ᵃ z₂}
                 (outBit-⊗ ξ₁ ξ₂ x₁ x₂ y₁ y₂) (λ _ → refl))
  (trans (same-++ (outBit ξ₁ x₁ y₁) (outBit ξ₂ x₂ y₂) z₁ z₂)
         (sym (cong₂ _∧_ (hits-same ξ₁ x₁ y₁ z₁)
                         (hits-same ξ₂ x₂ y₂ z₂)))))


------------------------------------------------------------------------
-- The amplitudes of a tensor

-- On a pair of paths the guard is a conjunction and the phase a sum;
-- the part of either path comes out as a rotation.

private
  guard-∧ : (a b : Bool) (e e′ : ℤ) →
            (if a ∧ b then zpow (e + e′) else 0ᴬ) ≐
            (if a then rot e (if b then zpow e′ else 0ᴬ) else 0ᴬ)
  guard-∧ true  b e e′   = ≐-sym (rot-if b e e′)
  guard-∧ false b e e′ _ = refl

  guard-∧′ : (a b : Bool) (e e′ : ℤ) →
             (if a ∧ b then zpow (e + e′) else 0ᴬ) ≐
             (if b then rot e′ (if a then zpow e else 0ᴬ) else 0ᴬ)
  guard-∧′ true  true  e e′   = zpow-≡ (+-comm e e′) ∙ ≐-sym (rot-zpow e′ e)
  guard-∧′ true  false e e′ _ = refl
  guard-∧′ false true  e e′   = ≐-sym (rot-0ᴬ e′)
  guard-∧′ false false e e′ _ = refl

-- The entry of U_{ξ₁⊗ξ₂} from x₁ x₂ to z₁ z₂, with U_ξ₁(x₁, z₁) written
-- out as its sum of powers of ζ multiplying U_ξ₂(x₂, z₂) ...

amp-⊗ʳ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
         (x₁ z₁ : Assign n₁) (x₂ z₂ : Assign n₂) →
         amp (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂) ≐
         Σᴮ (λ y₁ → if hits ξ₁ x₁ y₁ z₁
                    then rot (eval (phase ξ₁) x₁ y₁) (amp ξ₂ x₂ z₂)
                    else 0ᴬ)
amp-⊗ʳ {m₁ = m₁} {m₂ = m₂} ξ₁ ξ₂ x₁ z₁ x₂ z₂ =
  Σᴮ-++ m₁ m₂ (λ Y → if hits (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) Y (z₁ ++ᵃ z₂)
                     then zpow (eval (phase (ξ₁ ⊗ᴾ ξ₂)) (x₁ ++ᵃ x₂) Y)
                     else 0ᴬ)
  ∙ Σᴮ-cong per
  where
  per : ∀ y₁ →
        Σᴮ (λ y₂ → if hits (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂) (z₁ ++ᵃ z₂)
                   then zpow (eval (phase (ξ₁ ⊗ᴾ ξ₂)) (x₁ ++ᵃ x₂)
                                   (y₁ ++ᵃ y₂))
                   else 0ᴬ) ≐
        (if hits ξ₁ x₁ y₁ z₁
         then rot (eval (phase ξ₁) x₁ y₁) (amp ξ₂ x₂ z₂) else 0ᴬ)
  per y₁ =
    Σᴮ-cong (λ y₂ →
      if-cong (hits-⊗ ξ₁ ξ₂ x₁ z₁ x₂ z₂ y₁ y₂)
              (zpow-≡ (eval-⊗ ξ₁ ξ₂ x₁ x₂ y₁ y₂))
      ∙ guard-∧ (hits ξ₁ x₁ y₁ z₁) (hits ξ₂ x₂ y₂ z₂)
                (eval (phase ξ₁) x₁ y₁) (eval (phase ξ₂) x₂ y₂))
    ∙ ≐-sym (if-Σᴮ (hits ξ₁ x₁ y₁ z₁)
               (λ y₂ → rot (eval (phase ξ₁) x₁ y₁)
                           (if hits ξ₂ x₂ y₂ z₂
                            then zpow (eval (phase ξ₂) x₂ y₂) else 0ᴬ)))
    ∙ if-cong {p = hits ξ₁ x₁ y₁ z₁} refl
        (≐-sym (rot-Σᴮ (eval (phase ξ₁) x₁ y₁)
                  (λ y₂ → if hits ξ₂ x₂ y₂ z₂
                          then zpow (eval (phase ξ₂) x₂ y₂) else 0ᴬ)))

-- ... or with U_ξ₂(x₂, z₂) written out, multiplying U_ξ₁(x₁, z₁).

amp-⊗ʳ′ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
          (x₁ z₁ : Assign n₁) (x₂ z₂ : Assign n₂) →
          amp (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂) ≐
          Σᴮ (λ y₂ → if hits ξ₂ x₂ y₂ z₂
                     then rot (eval (phase ξ₂) x₂ y₂) (amp ξ₁ x₁ z₁)
                     else 0ᴬ)
amp-⊗ʳ′ {m₁ = m₁} {m₂ = m₂} ξ₁ ξ₂ x₁ z₁ x₂ z₂ =
  Σᴮ-++ m₁ m₂ (λ Y → if hits (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) Y (z₁ ++ᵃ z₂)
                     then zpow (eval (phase (ξ₁ ⊗ᴾ ξ₂)) (x₁ ++ᵃ x₂) Y)
                     else 0ᴬ)
  ∙ Σᴮ-cong (λ y₁ → Σᴮ-cong (λ y₂ →
      if-cong (hits-⊗ ξ₁ ξ₂ x₁ z₁ x₂ z₂ y₁ y₂)
              (zpow-≡ (eval-⊗ ξ₁ ξ₂ x₁ x₂ y₁ y₂))
      ∙ guard-∧′ (hits ξ₁ x₁ y₁ z₁) (hits ξ₂ x₂ y₂ z₂)
                 (eval (phase ξ₁) x₁ y₁) (eval (phase ξ₂) x₂ y₂)))
  ∙ Σᴮ-swap (λ y₁ y₂ → if hits ξ₂ x₂ y₂ z₂
                       then rot (eval (phase ξ₂) x₂ y₂)
                                (if hits ξ₁ x₁ y₁ z₁
                                 then zpow (eval (phase ξ₁) x₁ y₁) else 0ᴬ)
                       else 0ᴬ)
  ∙ Σᴮ-cong (λ y₂ →
      ≐-sym (if-Σᴮ (hits ξ₂ x₂ y₂ z₂)
               (λ y₁ → rot (eval (phase ξ₂) x₂ y₂)
                           (if hits ξ₁ x₁ y₁ z₁
                            then zpow (eval (phase ξ₁) x₁ y₁) else 0ᴬ)))
      ∙ if-cong {p = hits ξ₂ x₂ y₂ z₂} refl
          (≐-sym (rot-Σᴮ (eval (phase ξ₂) x₂ y₂)
                    (λ y₁ → if hits ξ₁ x₁ y₁ z₁
                            then zpow (eval (phase ξ₁) x₁ y₁) else 0ᴬ))))

-- U_{ξ₁⊗ξ₂} = U_ξ₁ ⊗ U_ξ₂: each entry is the product of the two
-- entries, in either order (PathSum.Ring does not prove ⊛
-- commutative).  Exact and unnormalised: the normalisations add.

amp-⊗ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
        (x₁ z₁ : Assign n₁) (x₂ z₂ : Assign n₂) →
        amp (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂) ≐
        amp ξ₁ x₁ z₁ ⊛ amp ξ₂ x₂ z₂
amp-⊗ ξ₁ ξ₂ x₁ z₁ x₂ z₂ =
  amp-⊗ʳ ξ₁ ξ₂ x₁ z₁ x₂ z₂ ∙ ≐-sym (amp-⊛ ξ₁ x₁ z₁ (amp ξ₂ x₂ z₂))

amp-⊗′ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
         (x₁ z₁ : Assign n₁) (x₂ z₂ : Assign n₂) →
         amp (ξ₁ ⊗ᴾ ξ₂) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂) ≐
         amp ξ₂ x₂ z₂ ⊛ amp ξ₁ x₁ z₁
amp-⊗′ ξ₁ ξ₂ x₁ z₁ x₂ z₂ =
  amp-⊗ʳ′ ξ₁ ξ₂ x₁ z₁ x₂ z₂ ∙ ≐-sym (amp-⊛ ξ₂ x₂ z₂ (amp ξ₁ x₁ z₁))

-- At states not written as concatenations: every state is the
-- concatenation of its blocks, and amplitudes read states only through
-- their values.  The sizes are explicit, since n₁ ℕ+ n₂ does not
-- determine n₁.

amp-blocks : ∀ n₁ n₂ (ξ : PathSum (n₁ ℕ+ n₂) k m)
             (x z : Assign (n₁ ℕ+ n₂)) →
             amp ξ x z ≐
             amp ξ (_++ᵃ_ {n₁} {n₂} (takeᵃ n₂ x) (dropᵃ n₁ x))
                   (_++ᵃ_ {n₁} {n₂} (takeᵃ n₂ z) (dropᵃ n₁ z))
amp-blocks n₁ n₂ ξ x z =
  amp-≗ˣ ξ {x} {_++ᵃ_ {n₁} {n₂} (takeᵃ n₂ x) (dropᵃ n₁ x)}
         (λ i → sym (++ᵃ-split n₁ n₂ x i)) z
  ∙ amp-≗ ξ (_++ᵃ_ {n₁} {n₂} (takeᵃ n₂ x) (dropᵃ n₁ x))
          {z} {_++ᵃ_ {n₁} {n₂} (takeᵃ n₂ z) (dropᵃ n₁ z)}
          (λ w → sym (++ᵃ-split n₁ n₂ z w))

amp-⊗-blocks : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
               (x z : Assign (n₁ ℕ+ n₂)) →
               amp (ξ₁ ⊗ᴾ ξ₂) x z ≐
               amp ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z) ⊛
               amp ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z)
amp-⊗-blocks {n₁ = n₁} {n₂ = n₂} ξ₁ ξ₂ x z =
  amp-blocks n₁ n₂ (ξ₁ ⊗ᴾ ξ₂) x z
  ∙ amp-⊗ ξ₁ ξ₂ (takeᵃ n₂ x) (takeᵃ n₂ z) (dropᵃ n₁ x) (dropᵃ n₁ z)


------------------------------------------------------------------------
-- An entry of U_ξ as a multiplier

-- Σ_y [f(x,y) = z] ζ^{P(x,y)} b, the entry of U_ξ from x to z times b
-- (PathSum.Compose.Matrix's amp-⊛), built without the product of
-- Z[ζ].  It is linear in b, and on a composite it is proposition 2.7.

private
  entry : PathSum n k m → Assign n → Assign n → Amp → Amp
  entry ξ x z b =
    Σᴮ (λ y → if hits ξ x y z then rot (eval (phase ξ) x y) b else 0ᴬ)

  entry-cong : (ξ : PathSum n k m) (x z : Assign n) {b b′ : Amp} →
               b ≐ b′ → entry ξ x z b ≐ entry ξ x z b′
  entry-cong ξ x z b≐b′ = Σᴮ-cong (λ y →
    if-cong {p = hits ξ x y z} refl (rot-map (eval (phase ξ) x y) b≐b′))

  entry-rot : (ξ : PathSum n k m) (x z : Assign n) (e : ℤ) (b : Amp) →
              entry ξ x z (rot e b) ≐ rot e (entry ξ x z b)
  entry-rot ξ x z e b =
    Σᴮ-cong (λ y →
      if-cong {p = hits ξ x y z} refl (rot-comm (eval (phase ξ) x y) e b)
      ∙ ≐-sym (rot-guard (hits ξ x y z) e (rot (eval (phase ξ) x y) b)))
    ∙ ≐-sym (rot-Σᴮ e (λ y → if hits ξ x y z
                             then rot (eval (phase ξ) x y) b else 0ᴬ))

  entry-Σᴮ : (ξ : PathSum n k m) (x z : Assign n)
             (g : (Fin j → Bool) → Amp) →
             entry ξ x z (Σᴮ g) ≐ Σᴮ (λ t → entry ξ x z (g t))
  entry-Σᴮ ξ x z g =
    Σᴮ-cong (λ y →
      if-cong {p = hits ξ x y z} refl (rot-Σᴮ (eval (phase ξ) x y) g)
      ∙ if-Σᴮ (hits ξ x y z) (λ t → rot (eval (phase ξ) x y) (g t)))
    ∙ Σᴮ-swap (λ y t → if hits ξ x y z
                       then rot (eval (phase ξ) x y) (g t) else 0ᴬ)

  scale-0ᴬ : ∀ i → scale i 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    _ = refl
  scale-0ᴬ (suc i)   = √2·-map (scale-0ᴬ i) ∙ √2·-0ᴬ

  entry-scale : (ξ : PathSum n k m) (x z : Assign n) (i : ℕ) (b : Amp) →
                scale i (entry ξ x z b) ≐ entry ξ x z (scale i b)
  entry-scale ξ x z i b =
    scale-Σᴮ i (λ y → if hits ξ x y z
                      then rot (eval (phase ξ) x y) b else 0ᴬ)
    ∙ Σᴮ-cong (λ y → guard y (hits ξ x y z))
    where
    guard : ∀ y c →
            scale i (if c then rot (eval (phase ξ) x y) b else 0ᴬ) ≐
            (if c then rot (eval (phase ξ) x y) (scale i b) else 0ᴬ)
    guard y true  = scale-rot i (eval (phase ξ) x y) b
    guard y false = scale-0ᴬ i

  -- Proposition 2.7 for the entry times b: split the composite's paths,
  -- and pull ζ^{P(x,y)} out of the sum over ξ′'s.

  entry-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) (x z : Assign n)
            (b : Amp) →
            entry (ξ′ ∘ᴾ ξ) x z b ≐
            Σᴮ (λ y → rot (eval (phase ξ) x y)
                          (entry ξ′ (outBit ξ x y) z b))
  entry-∘ {m′ = m′} {m = m} ξ′ ξ x z b =
    Σᴮ-++ m m′ (λ Y → if hits (ξ′ ∘ᴾ ξ) x Y z
                      then rot (eval (phase (ξ′ ∘ᴾ ξ)) x Y) b else 0ᴬ)
    ∙ Σᴮ-cong (λ y →
        Σᴮ-cong (λ y′ → point y y′)
        ∙ ≐-sym (rot-Σᴮ (eval (phase ξ) x y)
                  (λ y′ → if hits ξ′ (outBit ξ x y) y′ z
                          then rot (eval (phase ξ′) (outBit ξ x y) y′) b
                          else 0ᴬ)))
    where
    point : ∀ y y′ →
            (if hits (ξ′ ∘ᴾ ξ) x (y ++ᵃ y′) z
             then rot (eval (phase (ξ′ ∘ᴾ ξ)) x (y ++ᵃ y′)) b else 0ᴬ) ≐
            rot (eval (phase ξ) x y)
                (if hits ξ′ (outBit ξ x y) y′ z
                 then rot (eval (phase ξ′) (outBit ξ x y) y′) b else 0ᴬ)
    point y y′ =
      if-cong (hits-∘ ξ′ ξ x y y′ z)
        (rot-exp {eval (phase (ξ′ ∘ᴾ ξ)) x (y ++ᵃ y′)}
                 {eval (phase ξ) x y + eval (phase ξ′) (outBit ξ x y) y′}
                 b (eval-∘ ξ′ ξ x y y′)
         ∙ ≐-sym (rot-comp (eval (phase ξ) x y)
                           (eval (phase ξ′) (outBit ξ x y) y′) b))
      ∙ ≐-sym (rot-guard (hits ξ′ (outBit ξ x y) y′ z)
                         (eval (phase ξ) x y)
                         (rot (eval (phase ξ′) (outBit ξ x y) y′) b))

  -- The entries of a tensor at any pair of states, through either
  -- factor.

  amp-⊗-entry : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                (x z : Assign (n₁ ℕ+ n₂)) →
                amp (ξ₁ ⊗ᴾ ξ₂) x z ≐
                entry ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z)
                      (amp ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z))
  amp-⊗-entry {n₁ = n₁} {n₂ = n₂} ξ₁ ξ₂ x z =
    amp-blocks n₁ n₂ (ξ₁ ⊗ᴾ ξ₂) x z
    ∙ amp-⊗ʳ ξ₁ ξ₂ (takeᵃ n₂ x) (takeᵃ n₂ z) (dropᵃ n₁ x) (dropᵃ n₁ z)

  amp-⊗-entry′ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                 (x z : Assign (n₁ ℕ+ n₂)) →
                 amp (ξ₁ ⊗ᴾ ξ₂) x z ≐
                 entry ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z)
                       (amp ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z))
  amp-⊗-entry′ {n₁ = n₁} {n₂ = n₂} ξ₁ ξ₂ x z =
    amp-blocks n₁ n₂ (ξ₁ ⊗ᴾ ξ₂) x z
    ∙ amp-⊗ʳ′ ξ₁ ξ₂ (takeᵃ n₂ x) (takeᵃ n₂ z) (dropᵃ n₁ x) (dropᵃ n₁ z)


------------------------------------------------------------------------
-- The tensor respects ≋

-- In the lower factor: its amplitude is multiplied by an entry of the
-- upper one, which is linear, so the powers of √2 pass through it.

⊗ᴾ-congʳ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
           (η₂ : PathSum n₂ j′ l′) → ξ₂ ≋ η₂ → (ξ₁ ⊗ᴾ ξ₂) ≋ (ξ₁ ⊗ᴾ η₂)
⊗ᴾ-congʳ {n₁ = n₁} {k₁ = k₁} {n₂ = n₂} {k₂ = k₂} {j′ = j′}
         ξ₁ ξ₂ η₂ eq x z =
  scale-map (k₁ ℕ+ j′) (amp-⊗-entry ξ₁ ξ₂ x z)
  ∙ ≐-sym (scale-+ k₁ j′
             (entry ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z)
                    (amp ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z))))
  ∙ scale-map k₁ (entry-scale ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z) j′
                              (amp ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z)))
  ∙ scale-map k₁ (entry-cong ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z)
                             (eq (dropᵃ n₁ x) (dropᵃ n₁ z)))
  ∙ scale-map k₁ (≐-sym (entry-scale ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z) k₂
                                     (amp η₂ (dropᵃ n₁ x) (dropᵃ n₁ z))))
  ∙ scale-+ k₁ k₂ (entry ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z)
                         (amp η₂ (dropᵃ n₁ x) (dropᵃ n₁ z)))
  ∙ scale-map (k₁ ℕ+ k₂) (≐-sym (amp-⊗-entry ξ₁ η₂ x z))

-- In the upper factor, the same through the lower factor's entries.

⊗ᴾ-congˡ : (ξ₁ : PathSum n₁ k₁ m₁) (η₁ : PathSum n₁ j l)
           (ξ₂ : PathSum n₂ k₂ m₂) → ξ₁ ≋ η₁ → (ξ₁ ⊗ᴾ ξ₂) ≋ (η₁ ⊗ᴾ ξ₂)
⊗ᴾ-congˡ {n₁ = n₁} {k₁ = k₁} {j = j} {n₂ = n₂} {k₂ = k₂}
         ξ₁ η₁ ξ₂ eq x z =
  scale-map (j ℕ+ k₂) (amp-⊗-entry′ ξ₁ ξ₂ x z)
  ∙ scale-exp (entry ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z)
                     (amp ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z)))
              (ℕ.+-comm j k₂)
  ∙ ≐-sym (scale-+ k₂ j
             (entry ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z)
                    (amp ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z))))
  ∙ scale-map k₂ (entry-scale ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z) j
                              (amp ξ₁ (takeᵃ n₂ x) (takeᵃ n₂ z)))
  ∙ scale-map k₂ (entry-cong ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z)
                             (eq (takeᵃ n₂ x) (takeᵃ n₂ z)))
  ∙ scale-map k₂ (≐-sym (entry-scale ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z) k₁
                                     (amp η₁ (takeᵃ n₂ x) (takeᵃ n₂ z))))
  ∙ scale-+ k₂ k₁ (entry ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z)
                         (amp η₁ (takeᵃ n₂ x) (takeᵃ n₂ z)))
  ∙ scale-exp (entry ξ₂ (dropᵃ n₁ x) (dropᵃ n₁ z)
                     (amp η₁ (takeᵃ n₂ x) (takeᵃ n₂ z)))
              (ℕ.+-comm k₂ k₁)
  ∙ scale-map (k₁ ℕ+ k₂) (≐-sym (amp-⊗-entry′ η₁ ξ₂ x z))

-- In both at once.

⊗ᴾ-cong : (ξ₁ : PathSum n₁ k₁ m₁) (η₁ : PathSum n₁ j l)
          (ξ₂ : PathSum n₂ k₂ m₂) (η₂ : PathSum n₂ j′ l′) →
          ξ₁ ≋ η₁ → ξ₂ ≋ η₂ → (ξ₁ ⊗ᴾ ξ₂) ≋ (η₁ ⊗ᴾ η₂)
⊗ᴾ-cong ξ₁ η₁ ξ₂ η₂ eq₁ eq₂ =
  ≋-trans {ξ = ξ₁ ⊗ᴾ ξ₂} {ζ = η₁ ⊗ᴾ ξ₂} {χ = η₁ ⊗ᴾ η₂}
          (⊗ᴾ-congˡ ξ₁ η₁ ξ₂ eq₁) (⊗ᴾ-congʳ η₁ ξ₂ η₂ eq₂)


------------------------------------------------------------------------
-- Bifunctoriality (remark 2.8)

-- The tensor of two identities is the identity: its phase is 0 and
-- every output reads its own input.  The sizes are explicit, since
-- n₁ ℕ+ n₂ does not determine n₁.

⊗ᴾ-idPS : ∀ n₁ n₂ → (idPS {n₁} ⊗ᴾ idPS {n₂}) ≋ idPS {n₁ ℕ+ n₂}
⊗ᴾ-idPS n₁ n₂ =
  ≋-amp (idPS {n₁} ⊗ᴾ idPS {n₂}) (idPS {n₁ ℕ+ n₂}) refl
        (amp-ext (idPS {n₁} ⊗ᴾ idPS {n₂}) (idPS {n₁ ℕ+ n₂}) zero-phase
                 same-outputs)
  where
  zero-phase : ∀ x y → eval (phase (idPS {n₁} ⊗ᴾ idPS {n₂})) x y ≡
                       eval (phase (idPS {n₁ ℕ+ n₂})) x y
  zero-phase x y = trans (eval-⊗-blocks (idPS {n₁}) (idPS {n₂}) x y)
    (trans (cong₂ _+_ (eval-0ᴾ-val (takeᵃ n₂ x) (takeᵃ 0 y))
                      (eval-0ᴾ-val (dropᵃ n₁ x) (dropᵃ 0 y)))
           (sym (eval-0ᴾ-val x y)))

  same-outputs : ∀ x y w → outBit (idPS {n₁} ⊗ᴾ idPS {n₂}) x y w ≡
                           outBit (idPS {n₁ ℕ+ n₂}) x y w
  same-outputs x y = by-blocks n₁ n₂
    (λ i → trans (outBit-⊗ˡ (idPS {n₁}) (idPS {n₂}) x y i)
      (trans (outBit-μ idPS (takeᵃ n₂ x) (takeᵃ 0 y) i x[ i ] refl)
             (sym (outBit-μ idPS x y (i ↑ˡ n₂) x[ i ↑ˡ n₂ ] refl))))
    (λ i → trans (outBit-⊗ʳ (idPS {n₁}) (idPS {n₂}) x y i)
      (trans (outBit-μ idPS (dropᵃ n₁ x) (dropᵃ 0 y) i x[ i ] refl)
             (sym (outBit-μ idPS x y (n₁ ↑ʳ i) x[ n₁ ↑ʳ i ] refl))))

-- The left unit law: the identity on no wires, above ξ, is ξ.  Its
-- path-sum has ξ's indices on the nose, since 0 ℕ+ n is n.

⊗ᴾ-identityˡ : (ξ : PathSum n k m) → (idPS {0} ⊗ᴾ ξ) ≋ ξ
⊗ᴾ-identityˡ {n = n} {m = m} ξ =
  ≋-amp (idPS {0} ⊗ᴾ ξ) ξ refl
        (amp-ext (idPS {0} ⊗ᴾ ξ) ξ same-phase same-outputs)
  where
  same-phase : ∀ x y → eval (phase (idPS {0} ⊗ᴾ ξ)) x y ≡
                       eval (phase ξ) x y
  same-phase x y = trans (eval-⊗-blocks (idPS {0}) ξ x y)
    (trans (cong (_+ eval (phase ξ) x y)
                 (eval-0ᴾ-val (takeᵃ n x) (takeᵃ m y)))
           (+-identityˡ (eval (phase ξ) x y)))

  same-outputs : ∀ x y w → outBit (idPS {0} ⊗ᴾ ξ) x y w ≡ outBit ξ x y w
  same-outputs x y w = outBit-⊗ʳ (idPS {0}) ξ x y w

-- The interchange law.  At concatenated states both sides are
--
--   Σ_{y₁} Σ_{y₂} ζ^{P_ζ₁(x₁,y₁) + P_ζ₂(x₂,y₂)} ·
--     U_ξ₁(f_ζ₁(x₁,y₁), z₁) · U_ξ₂(f_ζ₂(x₂,y₂), z₂),
--
-- with U_ξ₁'s entry as a multiplier: on the left by proposition 2.7
-- for the composite of the two tensors and the evaluation of ζ₁ ⊗ ζ₂
-- along a pair of paths, on the right by amp-⊗ʳ, proposition 2.7 for
-- each factor, and the linearity of U_ξ₁'s entries.

private
  shuffle : ∀ a b c d → (a ℕ+ b) ℕ+ (c ℕ+ d) ≡ (a ℕ+ c) ℕ+ (b ℕ+ d)
  shuffle = solve 4 (λ a b c d →
    (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
    where open +-*-Solver using (solve; _:+_; _:=_)

  interchange-at :
    (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
    (ζ₁ : PathSum n₁ j₁ l₁) (ζ₂ : PathSum n₂ j₂ l₂)
    (x₁ z₁ : Assign n₁) (x₂ z₂ : Assign n₂) →
    amp ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂) ≐
    amp ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂)) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂)
  interchange-at {l₁ = l₁} {l₂ = l₂} ξ₁ ξ₂ ζ₁ ζ₂ x₁ z₁ x₂ z₂ =
    prop-2-7ʳ (ξ₁ ⊗ᴾ ξ₂) (ζ₁ ⊗ᴾ ζ₂) (x₁ ++ᵃ x₂) (z₁ ++ᵃ z₂)
    ∙ Σᴮ-++ l₁ l₂ (λ Y → rot (eval (phase (ζ₁ ⊗ᴾ ζ₂)) (x₁ ++ᵃ x₂) Y)
                             (amp (ξ₁ ⊗ᴾ ξ₂)
                                  (outBit (ζ₁ ⊗ᴾ ζ₂) (x₁ ++ᵃ x₂) Y)
                                  (z₁ ++ᵃ z₂)))
    ∙ Σᴮ-cong (λ y₁ → Σᴮ-cong (λ y₂ → left y₁ y₂))
    ∙ ≐-sym (Σᴮ-cong right)
    ∙ ≐-sym (entry-∘ ξ₁ ζ₁ x₁ z₁
               (Σᴮ (λ y₂ → rot (eval (phase ζ₂) x₂ y₂)
                               (amp ξ₂ (outBit ζ₂ x₂ y₂) z₂))))
    ∙ ≐-sym (entry-cong (ξ₁ ∘ᴾ ζ₁) x₁ z₁ (prop-2-7ʳ ξ₂ ζ₂ x₂ z₂))
    ∙ ≐-sym (amp-⊗ʳ (ξ₁ ∘ᴾ ζ₁) (ξ₂ ∘ᴾ ζ₂) x₁ z₁ x₂ z₂)
    where
    left : (y₁ : Assign l₁) (y₂ : Assign l₂) →
           rot (eval (phase (ζ₁ ⊗ᴾ ζ₂)) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂))
               (amp (ξ₁ ⊗ᴾ ξ₂) (outBit (ζ₁ ⊗ᴾ ζ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂))
                    (z₁ ++ᵃ z₂)) ≐
           rot (eval (phase ζ₁) x₁ y₁ + eval (phase ζ₂) x₂ y₂)
               (entry ξ₁ (outBit ζ₁ x₁ y₁) z₁
                      (amp ξ₂ (outBit ζ₂ x₂ y₂) z₂))
    left y₁ y₂ =
      rot-exp {eval (phase (ζ₁ ⊗ᴾ ζ₂)) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂)}
              {eval (phase ζ₁) x₁ y₁ + eval (phase ζ₂) x₂ y₂}
              (amp (ξ₁ ⊗ᴾ ξ₂) (outBit (ζ₁ ⊗ᴾ ζ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂))
                   (z₁ ++ᵃ z₂))
              (eval-⊗ ζ₁ ζ₂ x₁ x₂ y₁ y₂)
      ∙ rot-map (eval (phase ζ₁) x₁ y₁ + eval (phase ζ₂) x₂ y₂)
          (amp-≗ˣ (ξ₁ ⊗ᴾ ξ₂)
                  {outBit (ζ₁ ⊗ᴾ ζ₂) (x₁ ++ᵃ x₂) (y₁ ++ᵃ y₂)}
                  {outBit ζ₁ x₁ y₁ ++ᵃ outBit ζ₂ x₂ y₂}
                  (outBit-⊗ ζ₁ ζ₂ x₁ x₂ y₁ y₂) (z₁ ++ᵃ z₂)
           ∙ amp-⊗ʳ ξ₁ ξ₂ (outBit ζ₁ x₁ y₁) z₁ (outBit ζ₂ x₂ y₂) z₂)

    right : (y₁ : Assign l₁) →
            rot (eval (phase ζ₁) x₁ y₁)
                (entry ξ₁ (outBit ζ₁ x₁ y₁) z₁
                       (Σᴮ (λ y₂ → rot (eval (phase ζ₂) x₂ y₂)
                                       (amp ξ₂ (outBit ζ₂ x₂ y₂) z₂)))) ≐
            Σᴮ (λ y₂ → rot (eval (phase ζ₁) x₁ y₁ + eval (phase ζ₂) x₂ y₂)
                           (entry ξ₁ (outBit ζ₁ x₁ y₁) z₁
                                  (amp ξ₂ (outBit ζ₂ x₂ y₂) z₂)))
    right y₁ =
      rot-map (eval (phase ζ₁) x₁ y₁)
        (entry-Σᴮ ξ₁ (outBit ζ₁ x₁ y₁) z₁
           (λ y₂ → rot (eval (phase ζ₂) x₂ y₂)
                       (amp ξ₂ (outBit ζ₂ x₂ y₂) z₂))
         ∙ Σᴮ-cong (λ y₂ →
             entry-rot ξ₁ (outBit ζ₁ x₁ y₁) z₁ (eval (phase ζ₂) x₂ y₂)
                       (amp ξ₂ (outBit ζ₂ x₂ y₂) z₂)))
      ∙ rot-Σᴮ (eval (phase ζ₁) x₁ y₁)
          (λ y₂ → rot (eval (phase ζ₂) x₂ y₂)
                      (entry ξ₁ (outBit ζ₁ x₁ y₁) z₁
                             (amp ξ₂ (outBit ζ₂ x₂ y₂) z₂)))
      ∙ Σᴮ-cong (λ y₂ →
          rot-comp (eval (phase ζ₁) x₁ y₁) (eval (phase ζ₂) x₂ y₂)
                   (entry ξ₁ (outBit ζ₁ x₁ y₁) z₁
                          (amp ξ₂ (outBit ζ₂ x₂ y₂) z₂)))

amp-interchange : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                  (ζ₁ : PathSum n₁ j₁ l₁) (ζ₂ : PathSum n₂ j₂ l₂)
                  (x z : Assign (n₁ ℕ+ n₂)) →
                  amp ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)) x z ≐
                  amp ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂)) x z
amp-interchange {n₁ = n₁} {n₂ = n₂} ξ₁ ξ₂ ζ₁ ζ₂ x z =
  amp-blocks n₁ n₂ ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)) x z
  ∙ interchange-at ξ₁ ξ₂ ζ₁ ζ₂ (takeᵃ n₂ x) (takeᵃ n₂ z)
                   (dropᵃ n₁ x) (dropᵃ n₁ z)
  ∙ ≐-sym (amp-blocks n₁ n₂ ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂)) x z)

⊗-interchange : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂)
                (ζ₁ : PathSum n₁ j₁ l₁) (ζ₂ : PathSum n₂ j₂ l₂) →
                ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)) ≋ ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂))
⊗-interchange {k₁ = k₁} {k₂ = k₂} {j₁ = j₁} {j₂ = j₂} ξ₁ ξ₂ ζ₁ ζ₂ =
  ≋-amp ((ξ₁ ⊗ᴾ ξ₂) ∘ᴾ (ζ₁ ⊗ᴾ ζ₂)) ((ξ₁ ∘ᴾ ζ₁) ⊗ᴾ (ξ₂ ∘ᴾ ζ₂))
        (shuffle j₁ j₂ k₁ k₂) (amp-interchange ξ₁ ξ₂ ζ₁ ζ₂)

-- The law drawn in remark 2.8: ξ₁ on the upper wires and ξ₂ on the
-- lower ones, one after the other in either order, is ξ₁ ⊗ ξ₂.

⊗-sequential : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
               ((ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂)) ≋ (ξ₁ ⊗ᴾ ξ₂)
⊗-sequential {n₁ = n₁} {n₂ = n₂} ξ₁ ξ₂ =
  ≋-trans {ξ = (ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂)}
          {ζ = (ξ₁ ∘ᴾ idPS {n₁}) ⊗ᴾ (idPS {n₂} ∘ᴾ ξ₂)}
          {χ = ξ₁ ⊗ᴾ ξ₂}
    (⊗-interchange ξ₁ (idPS {n₂}) (idPS {n₁}) ξ₂)
    (⊗ᴾ-cong (ξ₁ ∘ᴾ idPS {n₁}) ξ₁ (idPS {n₂} ∘ᴾ ξ₂) ξ₂
             (∘ᴾ-identityʳ ξ₁) (∘ᴾ-identityˡ ξ₂))

⊗-sequential′ : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
                ((idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂})) ≋ (ξ₁ ⊗ᴾ ξ₂)
⊗-sequential′ {n₁ = n₁} {n₂ = n₂} ξ₁ ξ₂ =
  ≋-trans {ξ = (idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂})}
          {ζ = (idPS {n₁} ∘ᴾ ξ₁) ⊗ᴾ (ξ₂ ∘ᴾ idPS {n₂})}
          {χ = ξ₁ ⊗ᴾ ξ₂}
    (⊗-interchange (idPS {n₁}) ξ₂ ξ₁ (idPS {n₂}))
    (⊗ᴾ-cong (idPS {n₁} ∘ᴾ ξ₁) ξ₁ (ξ₂ ∘ᴾ idPS {n₂}) ξ₂
             (∘ᴾ-identityˡ ξ₁) (∘ᴾ-identityʳ ξ₂))

remark-2-8 : (ξ₁ : PathSum n₁ k₁ m₁) (ξ₂ : PathSum n₂ k₂ m₂) →
             ((ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂)) ≋
             ((idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂}))
remark-2-8 {n₁ = n₁} {n₂ = n₂} ξ₁ ξ₂ =
  ≋-trans {ξ = (ξ₁ ⊗ᴾ idPS {n₂}) ∘ᴾ (idPS {n₁} ⊗ᴾ ξ₂)}
          {ζ = ξ₁ ⊗ᴾ ξ₂}
          {χ = (idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂})}
    (⊗-sequential ξ₁ ξ₂)
    (≋-sym {ξ = (idPS {n₁} ⊗ᴾ ξ₂) ∘ᴾ (ξ₁ ⊗ᴾ idPS {n₂})}
           {ζ = ξ₁ ⊗ᴾ ξ₂}
           (⊗-sequential′ ξ₁ ξ₂))
