------------------------------------------------------------------------
-- Presentations of groups
--
-- Several ancillas prepared in |0⟩
--
-- PathSum.Ancilla restricts an equivalence of path-sums to the inputs
-- where one wire, an ancilla, is 0.  Section 5.2's n-bit Toffoli gates
-- use n - 3 ancillas at once, so here is the same for a family of
-- ancilla wires a : Fin j → Fin n (a need not be injective: only the
-- set of wires it lists matters).  An input x is clean when every
-- ancilla reads 0 (Clean a x), and
--
--    ξ ≋[ a ]₀* ζ  ⇔  ∀ x z, x clean → the entries of ξ and ζ from x to
--                     z agree (after normalisation)
--
-- which, for a one-element family, is PathSum.Ancilla's ξ ≋[ i ]₀ ζ
-- (≋[]₀⇔≋[]₀*).  It is a record, like PathSum.Classical's _computes_,
-- so that Agda compares two such statements by their arguments, never
-- by unfolding them into amplitudes.
--
-- As in PathSum.Ancilla, the path-sum of a circuit on clean inputs is
-- obtained by setting the ancillas to 0 in its polynomials (set0ˢ,
-- set0 once for each), which has the circuit's amplitudes at clean
-- inputs (amp-set0ˢ), so an equivalence proved of it holds on those
-- columns (set0ˢ-≋).  At any input, set0ˢ a ξ has the amplitudes of
-- ξ at that input with its ancillas set to 0 (amp-set0ˢ-any: a term
-- free of x_i does not read x_i, eval-∖-off), so the relation is
-- exactly full equivalence of the path-sums with the ancillas read as
-- the constant 0 (≋[]₀*⇔set0ˢ) -- the form in which the paper
-- computes with ancillas.  The relation follows from full equivalence
-- (≋⇒≋[]₀*), is carried along a full equivalence on the right
-- (≋[]₀*-≋), and holds between two path-sums computing functions that
-- agree on clean inputs (computes⇒≋[]₀*, the form in which section
-- 5.2's reversible circuits are verified).  "Leaves the ancillas
-- clean" is again a consequence: if every path of ζ from a clean input
-- outputs 0 on every ancilla, every amplitude of ξ from a clean input
-- to an output with some ancilla at 1 vanishes (clean-ancillas).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Ancillas (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; if_then_else_; not; _∧_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (_∈_)
open import Data.Integer.Base using (0ℤ; +_)
open import Data.Integer.Divisibility.Signed using (_∣?_)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

import Data.Fin.Properties as Fin
import Data.Fin.Subset.Properties as Subset

open import PathSum.AmpLinear M₀ using (scale-comm)
open import PathSum.Ancilla M₀ using
  (set0; amp-set0; eval-set0; _≋[_]₀_)
open import PathSum.Assign using (_[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using (_computes_; amp-computes; δ-≗)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; 0ᴬ; zpow; Σᴮ-cong; Σᴮ-0; √2·-map; √2·-0ᴬ; scale;
   scale-map; scale-injective)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; _≋_; hits-intro; hits-elim)
open import PathSum.Polynomial using
  (Poly; Mon; x[_]; eval; satᵐ; sat)
open import PathSum.Polynomial.Properties using
  (_∖ᵛ_; Σmon-cong; sat-cong-⊆)

private
  variable
    n k m k′ m′ k″ m″ j : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Clean inputs

-- Every ancilla reads 0.

Clean : (Fin j → Fin n) → Assign n → Set
Clean a x = ∀ i → x (a i) ≡ false


------------------------------------------------------------------------
-- Setting the ancillas to 0

-- PathSum.Ancilla's set0 at each ancilla in turn.

set0ˢ : (Fin j → Fin n) → PathSum n k m → PathSum n k m
set0ˢ {zero}  a ξ = ξ
set0ˢ {suc j} a ξ = set0ˢ (λ i → a (suc i)) (set0 (a zero) ξ)

-- At a clean input nothing dropped contributes.

amp-set0ˢ : (a : Fin j → Fin n) (ξ : PathSum n k m) (x z : Assign n) →
            Clean a x → amp (set0ˢ a ξ) x z ≐ amp ξ x z
amp-set0ˢ {zero}  a ξ x z cl i = refl
amp-set0ˢ {suc j} a ξ x z cl =
  amp-set0ˢ (λ i → a (suc i)) (set0 (a zero) ξ) x z (λ i → cl (suc i))
  ∙ amp-set0 ξ (a zero) x z (cl zero)


------------------------------------------------------------------------
-- The ancillas read as the constant 0, at every input

-- The terms free of x_i do not read x_i.

private
  if-0 : ∀ b → (if b then 0ℤ else 0ℤ) ≡ 0ℤ
  if-0 true  = refl
  if-0 false = refl

eval-∖-off : (P : Poly n m) (i : Fin n) {x x′ : Assign n} (y : Assign m) →
             (∀ j → j ≢ i → x j ≡ x′ j) →
             eval (P ∖ᵛ x[ i ]) x y ≡ eval (P ∖ᵛ x[ i ]) x′ y
eval-∖-off {n} {m} P i {x} {x′} y agree = Σmon-cong term
  where
  term : (γ : Mon n m) →
         (if satᵐ γ x y then (P ∖ᵛ x[ i ]) γ else 0ℤ) ≡
         (if satᵐ γ x′ y then (P ∖ᵛ x[ i ]) γ else 0ℤ)
  term (α , β) = go (i Subset.∈? α)
    where
    go : (d : Dec (i ∈ α)) →
         (if satᵐ (α , β) x y then (if ⌊ d ⌋ then 0ℤ else P (α , β))
          else 0ℤ) ≡
         (if satᵐ (α , β) x′ y then (if ⌊ d ⌋ then 0ℤ else P (α , β))
          else 0ℤ)
    go (yes _)  = trans (if-0 (satᵐ (α , β) x y))
                        (sym (if-0 (satᵐ (α , β) x′ y)))
    go (no i∉α) = cong (λ b → if b then P (α , β) else 0ℤ)
      (cong (_∧ sat β y) (sat-cong-⊆ α (λ j j∈α →
        agree j (λ j≡i → i∉α (subst (_∈ α) j≡i j∈α)))))

-- So dropping the terms containing x_i is evaluating with x_i = 0.

eval-set0-any : (P : Poly n m) (i : Fin n) (x : Assign n) (y : Assign m) →
                eval (P ∖ᵛ x[ i ]) x y ≡ eval P (x [ i ≔ false ]) y
eval-set0-any P i x y = trans
  (eval-∖-off P i y (λ j j≢i → sym (≔-there x false j≢i)))
  (eval-set0 P i (x [ i ≔ false ]) y (≔-here x i false))

-- Two path-sums whose paths give the same outputs hit the same z.

private
  hits-outBit : (ξ : PathSum n k m) (ζ : PathSum n k′ m) (x x′ : Assign n)
                (y : Assign m) (z : Assign n) →
                (∀ w → outBit ξ x y w ≡ outBit ζ x′ y w) →
                hits ξ x y z ≡ hits ζ x′ y z
  hits-outBit ξ ζ x x′ y z same = go (hits ζ x′ y z) refl
    where
    back : hits ξ x y z ≡ true → hits ζ x′ y z ≡ true
    back h = hits-intro ζ x′ y z (λ w →
      trans (sym (same w)) (hits-elim ξ x y z h w))

    flip : ∀ c → (c ≡ true → hits ζ x′ y z ≡ true) →
           hits ζ x′ y z ≡ false → c ≡ false
    flip false _ _ = refl
    flip true  f h = contradiction (trans (sym h) (f refl)) λ ()

    go : ∀ b → hits ζ x′ y z ≡ b → hits ξ x y z ≡ b
    go true  h = hits-intro ξ x y z (λ w →
      trans (same w) (hits-elim ζ x′ y z h w))
    go false h = flip (hits ξ x y z) back h

-- set0 i ξ at x is ξ at x with x_i set to 0 ...

amp-set0-any : (ξ : PathSum n k m) (i : Fin n) (x z : Assign n) →
               amp (set0 i ξ) x z ≐ amp ξ (x [ i ≔ false ]) z
amp-set0-any ξ i x z = Σᴮ-cong (λ y j →
  cong₂ (λ b e → (if b then zpow e else 0ᴬ) j)
        (hits-outBit (set0 i ξ) ξ x (x [ i ≔ false ]) y z (λ w →
           cong (λ e → not ⌊ (+ 2) ∣? e ⌋)
                (eval-set0-any (out ξ w) i x y)))
        (eval-set0-any (phase ξ) i x y))

-- ... and set0ˢ a ξ at x is ξ at x with every ancilla set to 0.

zeroˢ : (Fin j → Fin n) → Assign n → Assign n
zeroˢ {zero}  a x = x
zeroˢ {suc j} a x = zeroˢ (λ i → a (suc i)) x [ a zero ≔ false ]

clean-zeroˢ : (a : Fin j → Fin n) (x : Assign n) → Clean a (zeroˢ a x)
clean-zeroˢ {zero}  a x ()
clean-zeroˢ {suc j} a x zero    = ≔-here (zeroˢ (λ i → a (suc i)) x)
                                         (a zero) false
clean-zeroˢ {suc j} a x (suc i) =
  stay ⌊ a (suc i) Fin.≟ a zero ⌋ (clean-zeroˢ (λ i → a (suc i)) x i)
  where
  stay : ∀ d → zeroˢ (λ i → a (suc i)) x (a (suc i)) ≡ false →
         (if d then false else zeroˢ (λ i → a (suc i)) x (a (suc i))) ≡
         false
  stay true  _ = refl
  stay false h = h

amp-set0ˢ-any : (a : Fin j → Fin n) (ξ : PathSum n k m) (x z : Assign n) →
                amp (set0ˢ a ξ) x z ≐ amp ξ (zeroˢ a x) z
amp-set0ˢ-any {zero}  a ξ x z i = refl
amp-set0ˢ-any {suc j} a ξ x z =
  amp-set0ˢ-any (λ i → a (suc i)) (set0 (a zero) ξ) x z
  ∙ amp-set0-any ξ (a zero) (zeroˢ (λ i → a (suc i)) x) z


------------------------------------------------------------------------
-- Equivalence on the clean inputs

infix 4 _≋[_]₀*_

record _≋[_]₀*_ {n k m j k′ m′ : ℕ} (ξ : PathSum n k m)
                (a : Fin j → Fin n) (ζ : PathSum n k′ m′) : Set where
  constructor agree₀
  field
    amp-agree₀ : ∀ x z → Clean a x →
                 scale k′ (amp ξ x z) ≐ scale k (amp ζ x z)

open _≋[_]₀*_ public

-- For a single ancilla it is PathSum.Ancilla's relation.

≋[]₀⇔≋[]₀* : (i : Fin n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
             (ξ ≋[ i ]₀ ζ) ⇔ (ξ ≋[ (λ (_ : Fin 1) → i) ]₀* ζ)
≋[]₀⇔≋[]₀* i ξ ζ = mk⇔
  (λ eq → agree₀ λ x z cl → eq x z (cl zero))
  (λ eq x z x₀ → amp-agree₀ eq x z (λ _ → x₀))

-- Full equivalence implies it.

≋⇒≋[]₀* : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
          (a : Fin j → Fin n) → ξ ≋ ζ → ξ ≋[ a ]₀* ζ
≋⇒≋[]₀* a eq = agree₀ (λ x z _ → eq x z)

-- What is proved of the path-sum with the ancillas set to 0 holds of
-- the path-sum on the clean inputs.

set0ˢ-≋ : (a : Fin j → Fin n) (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
          set0ˢ a ξ ≋ ζ → ξ ≋[ a ]₀* ζ
set0ˢ-≋ {k′ = k′} a ξ ζ eq = agree₀ λ x z cl →
  scale-map k′ (≐-sym (amp-set0ˢ a ξ x z cl)) ∙ eq x z

-- It is exactly full equivalence once the ancillas are read as the
-- constant 0 on both sides.

≋[]₀*⇔set0ˢ : (a : Fin j → Fin n) (ξ : PathSum n k m)
              (ζ : PathSum n k′ m′) →
              (ξ ≋[ a ]₀* ζ) ⇔ (set0ˢ a ξ ≋ set0ˢ a ζ)
≋[]₀*⇔set0ˢ {k = k} {k′ = k′} a ξ ζ = mk⇔
  (λ eq x z →
     scale-map k′ (amp-set0ˢ-any a ξ x z)
     ∙ amp-agree₀ eq (zeroˢ a x) z (clean-zeroˢ a x)
     ∙ scale-map k (≐-sym (amp-set0ˢ-any a ζ x z)))
  (λ eq → agree₀ λ x z cl →
     scale-map k′ (≐-sym (amp-set0ˢ a ξ x z cl))
     ∙ eq x z
     ∙ scale-map k (amp-set0ˢ a ζ x z cl))

-- It can be carried along a full equivalence on the right.

≋[]₀*-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
          (χ : PathSum n k″ m″) (a : Fin j → Fin n) →
          ξ ≋[ a ]₀* ζ → ζ ≋ χ → ξ ≋[ a ]₀* χ
≋[]₀*-≋ {k = k} {k′ = k′} {k″ = k″} ξ ζ χ a eq₁ eq₂ = agree₀ λ x z cl →
  scale-injective k′ (scale k″ (amp ξ x z)) (scale k (amp χ x z))
    (scale-comm k′ k″ (amp ξ x z)
     ∙ scale-map k″ (amp-agree₀ eq₁ x z cl)
     ∙ scale-comm k″ k (amp ζ x z)
     ∙ scale-map k (eq₂ x z)
     ∙ scale-comm k k′ (amp χ x z))

-- Two path-sums computing functions that agree on the clean inputs
-- (PathSum.Classical) are equivalent there.

computes⇒≋[]₀* : (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
                 (a : Fin j → Fin n) {F G : Assign n → Assign n} →
                 ξ computes F → ζ computes G →
                 (∀ x → Clean a x → ∀ w → F x w ≡ G x w) →
                 ξ ≋[ a ]₀* ζ
computes⇒≋[]₀* {k = k} {k′ = k′} ξ ζ a {F} {G} cF cG h = agree₀ λ x z cl →
  scale-map k′ (amp-computes cF x z)
  ∙ scale-map k′ (scale-map k (δ-≗ (h x cl) z))
  ∙ scale-comm k′ k (δ (G x) z)
  ∙ scale-map k (≐-sym (amp-computes cG x z))


------------------------------------------------------------------------
-- Leaving the ancillas clean

private
  scale-0ᴬ : ∀ j → scale j 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    i = refl
  scale-0ᴬ (suc j) i = trans (√2·-map (scale-0ᴬ j) i) (√2·-0ᴬ i)

-- If every path of ζ from a clean input outputs 0 on every ancilla, no
-- path of ζ from a clean input reaches an output with an ancilla at 1,
-- so neither does ξ.

clean-ancillas : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
                 (a : Fin j → Fin n) → ξ ≋[ a ]₀* ζ →
                 (∀ x (y : Assign m′) → Clean a x →
                  ∀ i → outBit ζ x y (a i) ≡ false) →
                 ∀ x z → Clean a x → (i : Fin j) → z (a i) ≡ true →
                 amp ξ x z ≐ 0ᴬ
clean-ancillas {k = k} {k′ = k′} {m′ = m′} {ξ = ξ} {ζ} a eq out0
               x z cl i z₁ =
  scale-injective k′ (amp ξ x z) 0ᴬ
    (amp-agree₀ eq x z cl ∙ scale-map k amp0 ∙ scale-0ᴬ k
     ∙ ≐-sym (scale-0ᴬ k′))
  where
  miss : ∀ y → hits ζ x y z ≡ false
  miss y = flip (hits ζ x y z) λ h →
    trans (sym (out0 x y cl i)) (trans (hits-elim ζ x y z h (a i)) z₁)
    where
    flip : ∀ c → (c ≡ true → false ≡ true) → c ≡ false
    flip false _ = refl
    flip true  f = contradiction (f refl) λ ()

  amp0 : amp ζ x z ≐ 0ᴬ
  amp0 = Σᴮ-cong (λ y j′ →
           cong (λ b → (if b then zpow (eval (phase ζ) x y) else 0ᴬ) j′)
                (miss y))
         ∙ Σᴮ-0 {m′}
