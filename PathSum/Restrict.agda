------------------------------------------------------------------------
-- Presentations of groups
--
-- Isometry restrictions of arbitrary path-sums (Amy, QPL 2018,
-- section 4.1)
--
-- Section 4.1 checks a well-formed path-sum against the identity on
-- its isometry restriction ξ|f(x,y)=x, and reifies that restriction by
-- substitution: "if for some index i we have f_i(x,y) = y_i ⊕ Q(x,y)
-- where y_i doesn't appear in Q(x,y), we can substitute Q(x,y) for y_i
-- to get f_i(x,y) = x_i and remove y_i from the sum.  Any restrictions
-- which can't be reified are simply ignored."  PathSum.Gauss carries
-- this out when every output is a Z₂-linear (or affine) form, the
-- states of PathSum.CRK.Circuit; there elimination always reifies the
-- whole restriction or refutes.  This module does it for every
-- path-sum, whose outputs are arbitrary Boolean polynomials -- the
-- outputs of a composite such as the specification miter
-- ⟦ C † ⟧ ∘ᴾ ξ of section 3, of a hand-written specification, or of
-- anything else -- and makes "ignored" precise.
--
-- The plan.
--
--  1. Substitution at a path variable (substAt j P S = P[y_j ← S]):
--     the part of P free of y_j plus S times the quotient by y_j, over
--     the remaining variables.  Where S takes the value of a bit b, its
--     value is P's with y_j = b (eval-substAt).  PathSum.Reorder's _∖ʸ_
--     and _/ʸ_ split P at y_j (eval-insertᵃ).
--
--  2. A restriction step, semantically (Restricts ξ w j ρ).  Over every
--     path g of the reduct ρ the path-sum ξ has two paths, y_j = 0 and
--     y_j = 1.  The step names the one it keeps (keep x g); on the
--     other, wire w reads ¬x_w (miss); along the kept one every output
--     and the phase (modulo 1) are ρ's (outs, phase≡); and ρ's wire w
--     reads x_w (solves).  This is what the paper's substitution
--     y_j ← x_w ⊕ Q achieves when f_w = y_j ⊕ Q: the kept path is
--     y_j = x_w ⊕ Q, the other one reads f_w = ¬x_w.  The syntactic
--     step -- the substitution itself, from the hypothesis that f_w
--     is y_j ⊕ Q -- is PathSum.Restrict.Pivot.restrictᴾ, an instance;
--     the semantic form is what composites, whose polynomials are
--     opaque (PathSum.Polynomial.Bind), can be checked against.
--
--  3. What a step preserves (restricts-amp): every entry from x to a z
--     with z_w = x_w -- in particular the whole diagonal, i.e. the
--     isometry restriction -- but not the operator: the reduct is not
--     equivalent to ξ.  Along a chain of steps (_↝*_), every entry
--     from x to a z agreeing with x on the wires solved at the end
--     (restriction-amp); a solved wire stays solved (Solved-↝*).
--
--  4. Lemma 4.1 through the chain.  For WellFormed ξ and any chain of
--     restriction steps and rules of figure 2 (_⇝*_; the rules preserve
--     every entry up to normalisation, PathSum.Full.Sound),
--     ξ ≋ |x⟩ ↦ |x⟩ exactly when the end ρ satisfies the restriction
--     condition, Restriction-id ρ: amp ρ x x = √2^k for every x
--     (restriction-lemma-4-1).  That is the paper's "ignored": the
--     outputs left unsolved stay in ρ and still select its paths, and
--     the verdict is read on ρ's diagonal whatever they are.  When
--     every output of ρ is solved, ρ is diagonal and the condition is
--     ρ ≋ |x⟩ ↦ |x⟩ (restriction-solved, restriction-reified); when no
--     path variable is left it is too, solved or not, and then it is
--     syntactic (restriction-no-paths, restriction-syntactic).
--
--  5. Refutation (the analogue of PathSum.Gauss's refuted).  Where
--     some output of a reduct reads ¬x_w on every path from an input x,
--     the diagonal entry at x vanishes and ξ is not the identity, with
--     no well-formedness (restriction-refutes); syntactically, an
--     output free of path variables that is not x_w modulo 2 does so
--     at some input (restriction-refutes-syntactic).
--
-- Also here: every path-sum without path variables and normalisation
-- is WellFormed (noPaths-WellFormed) -- a classical specification such
-- as PathSum.Toffoli.Gate.toffoliˢ in particular -- and the
-- restriction condition is invariant under ≋ (Restriction-id-≋).
--
-- Companion modules: PathSum.Restrict.Pivot (the substitution itself,
-- from the paper's hypothesis f_w = y_j ⊕ Q; uniqueness of the reduct;
-- the procedure that stops when no pivot is left; the syntactic
-- refutation), PathSum.Restrict.Removes (a chain removes at most n
-- path variables), PathSum.Restrict.Linear (PathSum.Gauss's elimination
-- is a chain of these steps), PathSum.Restrict.Spec (the specification
-- miter), PathSum.CRK.WithX.WellFormed (circuits with X gates are well
-- formed), and the closed examples PathSum.Examples.Restrict and
-- PathSum.Examples.Restrict.NonLinear.
--
-- Departures and remarks.  The paper's "substitute Q(x,y) for y_i" is
-- the slip already noted in PathSum.Gauss: the substitution that makes
-- f_i read x_i is y_i ← x_i ⊕ Q.  The paper lets the output index and
-- the variable index coincide; any output and any path variable may
-- pivot here.  Unlike the linear case, a restriction step does not in
-- general keep the order of the phase (lemma 2.13 is for linear
-- substitutions, and PathSum.Polynomial.Substitution's header gives
-- the counterexample), so nothing here is about orders.  The paper's
-- restricted sum is a sum over the y with f(x,y) = x; here it is the
-- diagonal entry amp ρ x x, which is that sum (PathSum.Isometry).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Restrict (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ; *-identityˡ; *-zeroˡ; ≤-reflexive)
open import Data.Nat.Base using (zero; suc)
  renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (trans to ⇔-trans; sym to ⇔-sym)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; same; same-intro; same-true)
open import PathSum.AssignSum using
  (Σᶻ; RespectsZ; Σᶻ-cong; Σᶻ-0; Σᶻ-point)
open import PathSum.Anywhere.Sound M₀ using (Σᴮ-insert; hits-outBit)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; idPS)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; Σᴮ-cong; Σᴮ-+; Σᴮ-0; Respects; extend; zpow;
   zpow-cong; rot-zpow; scale; scale-map; scale-injective; zpow-0≢0ᴬ;
   √2·-map; √2·-injective; √2·-0ᴬ)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; _≋_; ≋-sym; hits-elim; hits-intro;
   hits-≗³; outBit-μ; eval-true; eval-false)
open import PathSum.Full M using (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_)
open import PathSum.Full.Sound M₀ using (⟶ᶠ-sound)
open import PathSum.Isometry M₀ using
  (WellFormed; Restriction-id; Diagonal; lemma-4-1; lemma-4-1⇒;
   diagonal-≋)
open import PathSum.Norm M₀ using (‖_‖²; ‖‖²-cong; ‖‖²-rot; ‖zpow0‖²; ‖0ᴬ‖²)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; x[_]; y[_]; μ; eval; _+ᴾ_; _-ᴾ_; _≈[_]_; NoVar; 0ᴾ)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-cong)
open import PathSum.Reorder using
  (insertᵃ; frontᴾ; _/ʸ_; _∖ʸ_; eval-front)
open import PathSum.Syntactic M₀ using (id⇔syntactic)

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Small facts

private
  if-cong : {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
            (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
  if-cong {p = true}  refl a≐b = a≐b
  if-cong {p = false} refl _   = λ _ → refl

  if-false : (p : Bool) (a : Amp) → p ≡ false → (if p then a else 0ᴬ) ≐ 0ᴬ
  if-false false _ _ _ = refl
  if-false true  _ () _

  zpow-≡ : {a b : ℤ} → a ≡ b → zpow a ≐ zpow b
  zpow-≡ refl _ = refl

  not-≢ : ∀ b → not b ≢ b
  not-≢ false ()
  not-≢ true  ()

  -- A Boolean other than b is not b.

  ≢⇒not : ∀ {a} b → a ≢ b → a ≡ not b
  ≢⇒not {false} false ne = contradiction refl ne
  ≢⇒not {false} true  _  = refl
  ≢⇒not {true}  false _  = refl
  ≢⇒not {true}  true  ne = contradiction refl ne

  -- √2^j ζ^0 is never zero (PathSum.Gauss proves it too, privately).

  scale-zpow0≢0 : ∀ j → ¬ (scale j (zpow 0ℤ) ≐ 0ᴬ)
  scale-zpow0≢0 zero    eq = zpow-0≢0ᴬ eq
  scale-zpow0≢0 (suc j) eq = scale-zpow0≢0 j
    (√2·-injective (scale j (zpow 0ℤ)) 0ᴬ
      (λ i → trans (eq i) (sym (√2·-0ᴬ i))))

  -- Scalings commute (Denotation proves the parts it needs privately).

  scale-+ : ∀ a b w → scale a (scale b w) ≐ scale (a ℕ+ b) w
  scale-+ zero    b w _ = refl
  scale-+ (suc a) b w   = √2·-map (scale-+ a b w)

  scale-exp : ∀ {a b} w → a ≡ b → scale a w ≐ scale b w
  scale-exp w refl _ = refl

  scale-comm : ∀ a b w → scale a (scale b w) ≐ scale b (scale a w)
  scale-comm a b w i =
    trans (scale-+ a b w i)
      (trans (scale-exp w (ℕ.+-comm a b) i) (sym (scale-+ b a w i)))


------------------------------------------------------------------------
-- Substitution at a path variable

-- P = (P ∖ʸ j) + y_j · (P /ʸ j): the value at an assignment with y_j
-- set to b.

eval-insertᵃ : (j : Fin (suc m)) (P : Poly n (suc m)) (x : Assign n)
               (g : Assign m) (b : Bool) →
               eval P x (insertᵃ j b g) ≡
               eval (P ∖ʸ j) x g + [ b ]ᶻ * eval (P /ʸ j) x g
eval-insertᵃ j P x g true = trans (sym (eval-front j P x (extend true g)))
  (trans (eval-true (frontᴾ j P) x g)
    (trans (+-comm (eval (P /ʸ j) x g) (eval (P ∖ʸ j) x g))
           (cong (λ t → eval (P ∖ʸ j) x g + t)
                 (sym (*-identityˡ (eval (P /ʸ j) x g))))))
eval-insertᵃ j P x g false = trans (sym (eval-front j P x (extend false g)))
  (trans (eval-false (frontᴾ j P) x g)
    (sym (trans (cong (λ t → eval (P ∖ʸ j) x g + t)
                      (*-zeroˡ (eval (P /ʸ j) x g)))
                (+-identityʳ (eval (P ∖ʸ j) x g)))))

-- P[y_j ← S], S over the remaining variables.

substAt : Fin (suc m) → Poly n (suc m) → Poly n m → Poly n m
substAt j P S = (P ∖ʸ j) +ᴾ (S *ᴾ (P /ʸ j))

-- Where S takes the value of a bit, substituting it is evaluating with
-- y_j set to that bit.

eval-substAt : (j : Fin (suc m)) (P : Poly n (suc m)) (S : Poly n m)
               (x : Assign n) (g : Assign m) (b : Bool) →
               eval S x g ≡ [ b ]ᶻ →
               eval (substAt j P S) x g ≡ eval P x (insertᵃ j b g)
eval-substAt j P S x g b eS = trans (eval-+ᴾ (P ∖ʸ j) (S *ᴾ (P /ʸ j)) x g)
  (trans (cong (λ t → eval (P ∖ʸ j) x g + t)
           (trans (eval-*ᴾ S (P /ʸ j) x g)
                  (cong (_* eval (P /ʸ j) x g) eS)))
         (sym (eval-insertᵃ j P x g b)))


------------------------------------------------------------------------
-- A restriction step

-- Wire w reads its input along every path.

Solved : PathSum n k m → Fin n → Set
Solved {n} {m = m} ρ w = ∀ (x : Assign n) (g : Assign m) → outBit ρ x g w ≡ x w

-- ρ is ξ restricted at wire w by eliminating y_j: of the two paths of
-- ξ over each path g of ρ, the one with y_j = keep x g is ρ's, and on
-- the other wire w misses its input.

record Restricts {n k m : ℕ} (ξ : PathSum n k (suc m)) (w : Fin n)
                 (j : Fin (suc m)) (ρ : PathSum n k m) : Set where
  field
    keep   : Assign n → Assign m → Bool
    miss   : ∀ x g → outBit ξ x (insertᵃ j (not (keep x g)) g) w ≡ not (x w)
    outs   : ∀ x g v → outBit ρ x g v ≡ outBit ξ x (insertᵃ j (keep x g) g) v
    solves : Solved ρ w
    phase≡ : ∀ x g → pow M ∣ (eval (phase ρ) x g -
                              eval (phase ξ) x (insertᵃ j (keep x g) g))

-- Every entry from x to a z agreeing with x on wire w is preserved.
-- The sum over the paths of ξ splits at y_j (Anywhere.Sound.Σᴮ-insert);
-- over each path g of ρ the kept path contributes ρ's term and the
-- other one nothing.

module _ {n k m : ℕ} {ξ : PathSum n k (suc m)} {w : Fin n}
         {j : Fin (suc m)} {ρ : PathSum n k m} (r : Restricts ξ w j ρ) where

  open Restricts r

  restricts-amp : ∀ x z → z w ≡ x w → amp ξ x z ≐ amp ρ x z
  restricts-amp x z zw i = trans (Σᴮ-insert j T respT i)
    (trans (sym (Σᴮ-+ (λ g → T (insertᵃ j true g))
                      (λ g → T (insertᵃ j false g)) i))
           (Σᴮ-cong per i))
    where
    T : Assign (suc m) → Amp
    T y = if hits ξ x y z then zpow (eval (phase ξ) x y) else 0ᴬ

    T′ : Assign m → Amp
    T′ g = if hits ρ x g z then zpow (eval (phase ρ) x g) else 0ᴬ

    respT : Respects T
    respT g h g≗h = if-cong
      (hits-≗³ ξ {x} {x} {g} {h} {z} {z} (λ _ → refl) g≗h (λ _ → refl))
      (zpow-≡ (eval-cong (phase ξ) {x} {x} {g} {h} (λ _ → refl) g≗h))

    live : ∀ g → T (insertᵃ j (keep x g) g) ≐ T′ g
    live g = if-cong
      (hits-outBit ξ ρ x (insertᵃ j (keep x g) g) g z
                   (λ v → sym (outs x g v)))
      (λ i → sym (zpow-cong {e = eval (phase ρ) x g}
                            {e′ = eval (phase ξ) x (insertᵃ j (keep x g) g)}
                            (phase≡ x g) i))

    dead : ∀ g → T (insertᵃ j (not (keep x g)) g) ≐ 0ᴬ
    dead g = if-false (hits ξ x y z) (zpow (eval (phase ξ) x y))
                      (no-hit (hits ξ x y z) refl)
      where
      y = insertᵃ j (not (keep x g)) g

      no-hit : ∀ h → hits ξ x y z ≡ h → h ≡ false
      no-hit false _ = refl
      no-hit true  e = contradiction
        (trans (sym (miss x g)) (trans (hits-elim ξ x y z e w) zw))
        (not-≢ (x w))

    per : ∀ g → (T (insertᵃ j true g) +ᴬ T (insertᵃ j false g)) ≐ T′ g
    per g = by (keep x g) refl
      where
      by : ∀ b → keep x g ≡ b →
           (T (insertᵃ j true g) +ᴬ T (insertᵃ j false g)) ≐ T′ g
      by true  eq i = trans
        (cong₂ _+_ (subst (λ c → T (insertᵃ j c g) ≐ T′ g) eq (live g) i)
                   (subst (λ c → T (insertᵃ j (not c) g) ≐ 0ᴬ) eq
                          (dead g) i))
        (+-identityʳ (T′ g i))
      by false eq i = trans
        (cong₂ _+_ (subst (λ c → T (insertᵃ j (not c) g) ≐ 0ᴬ) eq
                          (dead g) i)
                   (subst (λ c → T (insertᵃ j c g) ≐ T′ g) eq (live g) i))
        (+-identityˡ (T′ g i))

  -- The diagonal, i.e. the isometry restriction, in particular.

  restricts-diag : ∀ x → amp ξ x x ≐ amp ρ x x
  restricts-diag x = restricts-amp x x refl

  -- A wire that read its input along every path still does.

  restricts-Solved : ∀ v → Solved ξ v → Solved ρ v
  restricts-Solved v s x g = trans (outs x g v)
                                   (s x (insertᵃ j (keep x g) g))


------------------------------------------------------------------------
-- Chains of restriction steps

-- A step at some wire and path variable.

infix  4 _↝_ _↝*_
infixr 5 _◅ʳ_

data _↝_ {n k m : ℕ} (ξ : PathSum n k (suc m)) (ρ : PathSum n k m) : Set where
  step : (w : Fin n) (j : Fin (suc m)) → Restricts ξ w j ρ → ξ ↝ ρ

data _↝*_ {n k : ℕ} : ∀ {m m′} → PathSum n k m → PathSum n k m′ → Set where
  εʳ   : ∀ {m} {ξ : PathSum n k m} → ξ ↝* ξ
  _◅ʳ_ : ∀ {m m′} {ξ : PathSum n k (suc m)} {ρ : PathSum n k m}
         {ρ′ : PathSum n k m′} → ξ ↝ ρ → ρ ↝* ρ′ → ξ ↝* ρ′

-- Solved wires stay solved.

Solved-↝* : {ξ : PathSum n k m} {ρ : PathSum n k m′} → ξ ↝* ρ →
            ∀ v → Solved ξ v → Solved ρ v
Solved-↝* εʳ                     v s = s
Solved-↝* (step w j r ◅ʳ steps) v s =
  Solved-↝* steps v (restricts-Solved r v s)

-- Every entry from x to a z agreeing with x on the wires solved at the
-- end of the chain is preserved: each step's own wire is among them.

restriction-amp : {ξ : PathSum n k m} {ρ : PathSum n k m′} → ξ ↝* ρ →
                  ∀ x z → (∀ w → Solved ρ w → z w ≡ x w) →
                  amp ξ x z ≐ amp ρ x z
restriction-amp εʳ x z agree = λ _ → refl
restriction-amp (step w j r ◅ʳ steps) x z agree i = trans
  (restricts-amp r x z
    (agree w (Solved-↝* steps w (Restricts.solves r))) i)
  (restriction-amp steps x z agree i)

restriction-diag : {ξ : PathSum n k m} {ρ : PathSum n k m′} → ξ ↝* ρ →
                   ∀ x → amp ξ x x ≐ amp ρ x x
restriction-diag steps x = restriction-amp steps x x (λ _ _ → refl)


------------------------------------------------------------------------
-- Chains of restriction steps and rules of figure 2

infix  4 _⇝_ _⇝*_
infixr 5 _◅⇝_ _◅◅⇝_

data _⇝_ {n : ℕ} : ∀ {k m k′ m′} → PathSum n k m → PathSum n k′ m′ → Set where
  restrict : ∀ {k m} {ξ : PathSum n k (suc m)} {ρ : PathSum n k m} →
             ξ ↝ ρ → ξ ⇝ ρ
  rule     : ∀ {k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
             ξ ⟶ᶠ ζ → ξ ⇝ ζ

data _⇝*_ {n : ℕ} : ∀ {k m k′ m′} → PathSum n k m → PathSum n k′ m′ → Set where
  ε⇝   : ∀ {k m} {ξ : PathSum n k m} → ξ ⇝* ξ
  _◅⇝_ : ∀ {k m k′ m′ k″ m″} {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
         {χ : PathSum n k″ m″} → ξ ⇝ ζ → ζ ⇝* χ → ξ ⇝* χ

_◅◅⇝_ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} {χ : PathSum n k″ m″} →
        ξ ⇝* ζ → ζ ⇝* χ → ξ ⇝* χ
ε⇝          ◅◅⇝ rest = rest
(s ◅⇝ more) ◅◅⇝ rest = s ◅⇝ (more ◅◅⇝ rest)

-- Restriction chains and chains of rules are such chains.

↝*⇒⇝* : {ξ : PathSum n k m} {ρ : PathSum n k m′} → ξ ↝* ρ → ξ ⇝* ρ
↝*⇒⇝* εʳ           = ε⇝
↝*⇒⇝* (s ◅ʳ steps) = restrict s ◅⇝ ↝*⇒⇝* steps

⟶ᶠ*⇒⇝* : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ* ζ → ξ ⇝* ζ
⟶ᶠ*⇒⇝* εᶠ           = ε⇝
⟶ᶠ*⇒⇝* (s ◅ᶠ steps) = rule s ◅⇝ ⟶ᶠ*⇒⇝* steps


------------------------------------------------------------------------
-- The restriction condition along a chain

-- Equivalent path-sums satisfy the restriction condition together: ≋
-- relates the diagonals up to the two normalisations, and √2^k is
-- cancellable.

Restriction-id-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
                   Restriction-id ξ → Restriction-id ζ
Restriction-id-≋ {k = k} {k′ = k′} ξ ζ eq rid x =
  scale-injective k (amp ζ x x) (scale k′ (zpow 0ℤ)) (λ i →
    trans (sym (eq x x i))
      (trans (scale-map k′ (rid x) i) (scale-comm k′ k (zpow 0ℤ) i)))

private
  step-rid : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⇝ ζ →
             Restriction-id ξ ⇔ Restriction-id ζ
  step-rid {ξ = ξ} {ζ = ρ} (restrict (step w j r)) = mk⇔
    (λ rid x i → trans (sym (restricts-diag r x i)) (rid x i))
    (λ rid x i → trans (restricts-diag r x i) (rid x i))
  step-rid {ξ = ξ} {ζ = ζ} (rule s) = mk⇔
    (Restriction-id-≋ ξ ζ (⟶ᶠ-sound s))
    (Restriction-id-≋ ζ ξ (≋-sym {ξ = ξ} {ζ = ζ} (⟶ᶠ-sound s)))

chain-rid : {ξ : PathSum n k m} {ρ : PathSum n k′ m′} → ξ ⇝* ρ →
            Restriction-id ξ ⇔ Restriction-id ρ
chain-rid ε⇝           = mk⇔ (λ r → r) (λ r → r)
chain-rid (s ◅⇝ steps) = ⇔-trans (step-rid s) (chain-rid steps)


------------------------------------------------------------------------
-- Lemma 4.1 through a chain

-- For a well-formed ξ the verdict is read off the diagonal of the end
-- of any chain, whatever outputs it left unsolved.

restriction-lemma-4-1 : (ξ : PathSum n k m) {ρ : PathSum n k′ m′} →
                        WellFormed ξ → ξ ⇝* ρ →
                        (ξ ≋ idPS ⇔ Restriction-id ρ)
restriction-lemma-4-1 ξ wf steps =
  ⇔-trans (lemma-4-1 ξ wf) (chain-rid steps)

-- The brief form, for chains of restriction steps alone.

restriction-lemma-4-1ʳ : (ξ : PathSum n k m) {ρ : PathSum n k m′} →
                         WellFormed ξ → ξ ↝* ρ →
                         (ξ ≋ idPS ⇔ Restriction-id ρ)
restriction-lemma-4-1ʳ ξ wf steps =
  restriction-lemma-4-1 ξ wf (↝*⇒⇝* steps)

-- Once every output is solved the end is diagonal, and the condition
-- is that it is the identity.

Solved⇒Diagonal : (ρ : PathSum n k m) → (∀ w → Solved ρ w) → Diagonal ρ
Solved⇒Diagonal ρ solved x y z h = same-intro x z (λ w →
  trans (sym (solved w x y)) (hits-elim ρ x y z h w))

restriction-solved : (ξ : PathSum n k m) (ρ : PathSum n k′ m′) →
                     WellFormed ξ → ξ ⇝* ρ → (∀ w → Solved ρ w) →
                     (ξ ≋ idPS ⇔ ρ ≋ idPS)
restriction-solved ξ ρ wf steps solved =
  ⇔-trans (restriction-lemma-4-1 ξ wf steps)
          (⇔-sym (diagonal-≋ ρ (Solved⇒Diagonal ρ solved)))

-- In particular once every output is the input variable.

restriction-reified : (ξ : PathSum n k m) (ρ : PathSum n k′ m′) →
                      WellFormed ξ → ξ ⇝* ρ → (∀ w → out ρ w ≡ μ x[ w ]) →
                      (ξ ≋ idPS ⇔ ρ ≋ idPS)
restriction-reified ξ ρ wf steps outs =
  restriction-solved ξ ρ wf steps (λ w x g → outBit-μ ρ x g w x[ w ] (outs w))


------------------------------------------------------------------------
-- No path variables left

-- With no path variable, a path-sum that satisfies the restriction
-- condition has its single path return every input: the diagonal entry
-- would otherwise be 0, which √2^k ζ^0 is not.  So it is diagonal,
-- whatever its outputs look like.

private
  none : Assign 0
  none ()

  -- With no path variable the amplitude is its single term, read at
  -- the empty assignment.

  amp-none : (ρ : PathSum n k 0) (x z : Assign n) →
             amp ρ x z ≐
             (if hits ρ x none z then zpow (eval (phase ρ) x none) else 0ᴬ)
  amp-none ρ x z = Σᴮ-cong
    {f = λ y → if hits ρ x y z then zpow (eval (phase ρ) x y) else 0ᴬ}
    {g = λ _ → if hits ρ x none z then zpow (eval (phase ρ) x none) else 0ᴬ}
    (λ y → if-cong
      (hits-≗³ ρ {x} {x} {y} {none} {z} {z} (λ _ → refl) (λ ()) (λ _ → refl))
      (zpow-≡ (eval-cong (phase ρ) {x} {x} {y} {none} (λ _ → refl) (λ ()))))

rid-no-paths⇒Diagonal : (ρ : PathSum n k 0) → Restriction-id ρ → Diagonal ρ
rid-no-paths⇒Diagonal {k = k} ρ rid x y z h = same-intro x z (λ w →
  trans (sym (back w)) (hits-elim ρ x y z h w))
  where
  hit : hits ρ x none x ≡ true
  hit = by (hits ρ x none x) refl
    where
    by : ∀ b → hits ρ x none x ≡ b → b ≡ true
    by true  _ = refl
    by false e = contradiction
      (λ i → trans (sym (rid x i)) (trans (amp-none ρ x x i)
        (if-false (hits ρ x none x) (zpow (eval (phase ρ) x none)) e i)))
      (scale-zpow0≢0 k)

  back : ∀ w → outBit ρ x y w ≡ x w
  back w = trans (cong (λ b → not ⌊ (+ 2) ∣? b ⌋)
                       (eval-cong (out ρ w) {x} {x} {y} {none}
                                  (λ _ → refl) (λ ())))
                 (hits-elim ρ x none x hit w)

restriction-no-paths : (ξ : PathSum n k m) (ρ : PathSum n k′ 0) →
                       WellFormed ξ → ξ ⇝* ρ → (ξ ≋ idPS ⇔ ρ ≋ idPS)
restriction-no-paths ξ ρ wf steps = mk⇔
  (λ eq → Equivalence.from (diagonal-≋ ρ (rid-no-paths⇒Diagonal ρ (rid eq)))
                           (rid eq))
  (λ eq → Equivalence.from (restriction-lemma-4-1 ξ wf steps)
                           (lemma-4-1⇒ ρ eq))
  where
  rid : ξ ≋ idPS → Restriction-id ρ
  rid = Equivalence.to (restriction-lemma-4-1 ξ wf steps)

-- And then the verdict is syntactic (PathSum.Syntactic).

restriction-syntactic : (ξ : PathSum n k m) (ρ : PathSum n k′ 0) →
                        WellFormed ξ → ξ ⇝* ρ →
                        (ξ ≋ idPS ⇔
                         (k′ ≡ 0 ×
                          (∀ w → out ρ w ≈[ + 2 ] μ x[ w ]) ×
                          phase ρ ≈[ pow M ] 0ᴾ))
restriction-syntactic ξ ρ wf steps =
  ⇔-trans (restriction-no-paths ξ ρ wf steps) (id⇔syntactic ρ)


------------------------------------------------------------------------
-- Refutation

-- An output that reads ¬x_w on every path from x kills the diagonal
-- entry at x, and with it the identity, at the end of any chain and so
-- at its start.  No well-formedness is needed.

amp-miss : (ρ : PathSum n k m) (w : Fin n) (x : Assign n) →
           (∀ y → outBit ρ x y w ≡ not (x w)) → amp ρ x x ≐ 0ᴬ
amp-miss {m = m} ρ w x miss i = trans (Σᴮ-cong term i) (Σᴮ-0 {m} i)
  where
  term : ∀ y → (if hits ρ x y x then zpow (eval (phase ρ) x y) else 0ᴬ) ≐ 0ᴬ
  term y = if-false (hits ρ x y x) (zpow (eval (phase ρ) x y))
                    (no-hit (hits ρ x y x) refl)
    where
    no-hit : ∀ h → hits ρ x y x ≡ h → h ≡ false
    no-hit false _ = refl
    no-hit true  e = contradiction
      (trans (sym (miss y)) (hits-elim ρ x y x e w)) (not-≢ (x w))

restriction-refutes-amp : (ξ : PathSum n k m) (ρ : PathSum n k′ m′) →
                          ξ ⇝* ρ → (x : Assign n) → amp ρ x x ≐ 0ᴬ →
                          ¬ (ξ ≋ idPS)
restriction-refutes-amp {k′ = k′} ξ ρ steps x z eq =
  scale-zpow0≢0 k′ (λ i →
    trans (sym (Equivalence.to (chain-rid steps) (lemma-4-1⇒ ξ eq) x i))
          (z i))

restriction-refutes : (ξ : PathSum n k m) (ρ : PathSum n k′ m′) →
                      ξ ⇝* ρ → (w : Fin n) (x : Assign n) →
                      (∀ y → outBit ρ x y w ≡ not (x w)) → ¬ (ξ ≋ idPS)
restriction-refutes ξ ρ steps w x miss =
  restriction-refutes-amp ξ ρ steps x (amp-miss ρ w x miss)

-- Once every output is solved, anything that refutes the end -- lemma
-- 4.2, say -- refutes the start, again with no well-formedness: the
-- end is diagonal, so it is the identity exactly when its diagonal is.

restriction-refutes-solved : (ξ : PathSum n k m) (ρ : PathSum n k′ m′) →
                             ξ ⇝* ρ → (∀ w → Solved ρ w) →
                             ¬ (ρ ≋ idPS) → ¬ (ξ ≋ idPS)
restriction-refutes-solved ξ ρ steps solved ne eq =
  ne (Equivalence.from (diagonal-≋ ρ (Solved⇒Diagonal ρ solved))
       (Equivalence.to (chain-rid steps) (lemma-4-1⇒ ξ eq)))


------------------------------------------------------------------------
-- Path-sums without paths are well formed

-- A column of a path-sum with no path variable and no normalisation
-- has a single entry, a power of ζ, at the state its path reaches.  So
-- every classical specification is WellFormed.

private
  ‖zpow‖² : ∀ e → ‖ zpow e ‖² ≡ 1ℤ
  ‖zpow‖² e = trans (‖‖²-cong {zpow e} {zpow (e + 0ℤ)}
                               (zpow-≡ (sym (+-identityʳ e))))
    (trans (‖‖²-cong {zpow (e + 0ℤ)} {_} (λ i → sym (rot-zpow e 0ℤ i)))
           (trans (‖‖²-rot e (zpow 0ℤ)) ‖zpow0‖²))

noPaths-WellFormed : (ξ : PathSum n 0 0) → WellFormed ξ
noPaths-WellFormed {n} ξ x = ≤-reflexive
  (trans (Σᶻ-point f resp z₀)
    (trans (cong₂ _+_ at-z₀ (trans (Σᶻ-cong rest) Σᶻ-0))
           (+-identityʳ 1ℤ)))
  where
  e : ℤ
  e = eval (phase ξ) x none

  f : Assign n → ℤ
  f z = ‖ amp ξ x z ‖²

  resp : RespectsZ f
  resp z z′ zz = ‖‖²-cong {amp ξ x z} {amp ξ x z′} (λ i →
    trans (amp-none ξ x z i) (trans
      (cong (λ b → (if b then zpow e else 0ᴬ) i)
            (hits-≗³ ξ {x} {x} {none} {none} {z} {z′} (λ _ → refl)
                     (λ ()) zz))
      (sym (amp-none ξ x z′ i))))

  z₀ : Assign n
  z₀ = outBit ξ x none

  at-z₀ : f z₀ ≡ 1ℤ
  at-z₀ = trans (‖‖²-cong {amp ξ x z₀} {zpow e} (λ i →
      trans (amp-none ξ x z₀ i)
        (cong (λ b → (if b then zpow e else 0ᴬ) i)
              (hits-intro ξ x none z₀ (λ _ → refl)))))
    (‖zpow‖² e)

  rest : ∀ z → (if same z₀ z then 0ℤ else f z) ≡ 0ℤ
  rest z = by (same z₀ z) refl
    where
    by : ∀ b → same z₀ z ≡ b → (if b then 0ℤ else f z) ≡ 0ℤ
    by true  _  = refl
    by false ne = trans (‖‖²-cong {amp ξ x z} {0ᴬ} (λ i →
        trans (amp-none ξ x z i)
          (if-false (hits ξ x none z) (zpow e)
                    (miss (hits ξ x none z) refl) i)))
      ‖0ᴬ‖²
      where
      miss : ∀ h → hits ξ x none z ≡ h → h ≡ false
      miss false _ = refl
      miss true  h = contradiction
        (trans (sym ne) (same-intro z₀ z (hits-elim ξ x none z h)))
        (λ ())
