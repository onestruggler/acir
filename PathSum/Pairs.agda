------------------------------------------------------------------------
-- Presentations of groups
--
-- Interference of two and of four branches of a path-sum
--
-- Every rule of figure 2 in Amy's "Towards Large-scale Functional
-- Verification of Universal Quantum Circuits" (QPL 2018) is sound
-- because the branches of the eliminated path variables interfere:
-- summing over y₀ pairs each path with the one differing from it at
-- y₀, and the pair contributes ζ^(h+t) + ζ^t, where t is the phase
-- without y₀ and h the coefficient of y₀.  What the pair adds up to
-- depends only on h modulo 1 (the numerator modulo 2^M):
--
--   h ≡ 0         2ζ^t                 ([Elim], and [HH] where Q = y_i)
--   h ≡ ½         0                    ([HH] where Q ≠ y_i, lemma 4.2)
--   h ≡ ¼         √2 ζ^(⅛ + t)         ([ω] where Q = 0)
--   h ≡ ¼ + ½     √2 ζ^(⅛ - ¼ + t)     ([ω] where Q = 1)
--
-- PathSum.Denotation proves these for its own rules, privately; they
-- are proved again here, as statements about integers and amplitudes
-- that mention no rule, so that the general rules (and lemma 4.2 for
-- general quotients) can use them without reopening Denotation.  The
-- pair over y₀ of a path-sum as a whole is Denotation's public
-- Branches, extended here by module Pair; the quadruple over y₀ and y₁
-- that [Case] needs is module Quad, and quad is the identity it rests
-- on: when the y₀y₁ coefficient is ½, the four branches add up to
-- twice a single power of ζ, whichever of the paper's two
-- decompositions X selects.
--
-- One more thing Denotation keeps private is how an output is read:
-- hits-eval says that two path-sums whose outputs take the same values
-- at two paths hit the same states there.  It rests on the reading of
-- an output being, definitionally, its value's parity (outBit), which
-- private definitions still reduce to.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Pairs (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣-refl; ∣m∣n⇒∣m+n; ∣n⇒∣m*n)
open import Data.Integer.Properties using (+-inverseˡ; +-comm)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (_∷_; there)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; y₀; head-part; tail-part)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; 0ᴬ; _+ᴬ_; _·ᴬ_; -ᴬ_; zpow; zpow-cong; zpow-anti; √2·;
   √2·-zpow; √2·-0ᴬ; Σᴮ; Σᴮ-+; extend; Respects)
  renaming (c to cᶻ; H to Hᶻ; N to Nᶻ)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; hits-intro; hits-elim; hits-≗³; same-hits;
   eval-true; eval-false; module Branches)
open import PathSum.Polynomial using (y[_]; NoVar; eval)
open import PathSum.Polynomial.Boolean using (IsBit)
open import PathSum.Polynomial.Properties using (eval-cong)
open import PathSum.Polynomial.Substitution using (q₀₀; q₀₁; q₁₀; q₁₁)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Order M using (pow; pow-suc; parity)
open import PathSum.Reduction M using (⅛; ¼; ½)

import Relation.Binary.PropositionalEquality as Eq

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- The dyadic constants

-- ⅛ + ⅛ = ¼ and so on, the numerators being consecutive powers of 2;
-- and the numerator of 1 is 2^M.

private
  double : ∀ u → u + u ≡ u * (+ 2)
  double = solve 1 (λ u → u :+ u := u :* con (+ 2)) refl

  twice : ∀ u → u + u ≡ (+ 2) * u
  twice = solve 1 (λ u → u :+ u := con (+ 2) :* u) refl

  ⅛+⅛ : ⅛ + ⅛ ≡ ¼
  ⅛+⅛ = trans (double ⅛) (sym (pow-suc M₀))

  ¼+¼ : ¼ + ¼ ≡ ½
  ¼+¼ = trans (double ¼) (sym (pow-suc (suc M₀)))

  ½·2 : ½ * (+ 2) ≡ pow M
  ½·2 = sym (pow-suc (suc (suc M₀)))

  ½+½ : ½ + ½ ≡ pow M
  ½+½ = trans (double ½) ½·2

  -- Congruence modulo 2^M is what zpow-cong asks for.
  by-∣ : ∀ {D} e e′ → pow M ∣ D → e - e′ ≡ D → zpow e ≐ zpow e′
  by-∣ e e′ d eq = zpow-cong {e} {e′} (Eq.subst ((+ Nᶻ) ∣_) (sym eq) d)


------------------------------------------------------------------------
-- Halving

-- A congruence h ≡ ½·s modulo 2^M fixes h modulo 1 to 0 or ½ according
-- to the parity of s: half an even number is a whole one.

half-even : ∀ {h s : ℤ} → pow M ∣ (h - (½ * s)) → (+ 2) ∣ s → pow M ∣ h
half-even {h} {s} d (divides r s≡) =
  Eq.subst (pow M ∣_) (restore h (½ * s)) (∣m∣n⇒∣m+n d half)
  where
  restore : ∀ a b → (a - b) + b ≡ a
  restore = solve 2 (λ a b → (a :- b) :+ b := a) refl

  swap : ∀ u r → u * (r * (+ 2)) ≡ r * (u * (+ 2))
  swap = solve 2 (λ u r → u :* (r :* con (+ 2)) := r :* (u :* con (+ 2)))
                 refl

  half : pow M ∣ (½ * s)
  half = Eq.subst (pow M ∣_)
    (sym (trans (cong (λ u → ½ * u) s≡)
                (trans (swap ½ r) (cong (λ u → r * u) ½·2))))
    (∣n⇒∣m*n r ∣-refl)

half-odd : ∀ {h s : ℤ} → pow M ∣ (h - (½ * s)) → ¬ ((+ 2) ∣ s) →
           pow M ∣ (h - ½)
half-odd {h} {s} d ¬2∣s with parity s
... | inj₁ (r , s≡) = contradiction (divides r s≡) ¬2∣s
... | inj₂ (r , s≡) =
  Eq.subst (pow M ∣_) (sym shape) (∣m∣n⇒∣m+n d (∣n⇒∣m*n r ∣-refl))
  where
  expand : ∀ h t r →
           h - t ≡ (h - (t * ((r * (+ 2)) + 1ℤ))) + (r * (t * (+ 2)))
  expand = solve 3 (λ h t r →
    h :- t :=
    (h :- (t :* ((r :* con (+ 2)) :+ con 1ℤ))) :+ (r :* (t :* con (+ 2))))
    refl

  shape : h - ½ ≡ (h - (½ * s)) + (r * pow M)
  shape = trans (expand h ½ r)
    (cong₂ (λ u w → (h - (½ * u)) + (r * w)) (sym s≡) ½·2)


------------------------------------------------------------------------
-- Pairs of powers of ζ

-- The four ways two branches of y₀ interfere, h being the coefficient
-- of y₀ and t the rest of the phase.

pair-double : (h t : ℤ) → pow M ∣ h → (zpow (h + t) +ᴬ zpow t) ≐ (+ 2) ·ᴬ zpow t
pair-double h t d i = trans
  (cong (λ u → u + zpow t i) (by-∣ (h + t) t d (shift h t) i))
  (twice (zpow t i))
  where
  shift : ∀ a t → (a + t) - t ≡ a
  shift = solve 2 (λ a t → (a :+ t) :- t := a) refl

-- ζ^(½) = -1.

pair-cancel : (h t : ℤ) → pow M ∣ (h - ½) → (zpow (h + t) +ᴬ zpow t) ≐ 0ᴬ
pair-cancel h t d i = trans
  (cong (λ u → u + zpow t i)
    (trans (by-∣ (h + t) (t + (+ Hᶻ)) d (shuffle h ½ t) i) (zpow-anti t i)))
  (+-inverseˡ (zpow t i))
  where
  shuffle : ∀ a b t → (a + t) - (t + b) ≡ a - b
  shuffle = solve 3 (λ a b t → (a :+ t) :- (t :+ b) := a :- b) refl

-- √2 = ζ^⅛ + ζ^(-⅛), so √2·ζ^(⅛+t) = ζ^(¼+t) + ζ^t and
-- √2·ζ^(⅛-¼+t) = ζ^t + ζ^(-¼+t); and -¼ ≡ ¼ + ½ modulo 1.

private
  cancel-neg : ∀ u t → (- u) + (u + t) ≡ t
  cancel-neg = solve 2 (λ u t → (:- u) :+ (u :+ t) := t) refl

  pull : ∀ u t → u + (u + t) ≡ (u + u) + t
  pull = solve 2 (λ u t → u :+ (u :+ t) := (u :+ u) :+ t) refl

pair-ω₀ : (h t : ℤ) → pow M ∣ (h - ¼) →
          (zpow (h + t) +ᴬ zpow t) ≐ √2· (zpow (⅛ + t))
pair-ω₀ h t d i = trans
  (cong (λ u → u + zpow t i) (by-∣ (h + t) (¼ + t) d (drop-t h ¼ t) i))
  (sym split)
  where
  drop-t : ∀ a b t → (a + t) - (b + t) ≡ a - b
  drop-t = solve 3 (λ a b t → (a :+ t) :- (b :+ t) := a :- b) refl

  up : (+ cᶻ) + (⅛ + t) ≡ ¼ + t
  up = trans (pull ⅛ t) (cong (λ u → u + t) ⅛+⅛)

  down : (- (+ cᶻ)) + (⅛ + t) ≡ t
  down = cancel-neg ⅛ t

  split : √2· (zpow (⅛ + t)) i ≡ zpow (¼ + t) i + zpow t i
  split = trans (√2·-zpow (⅛ + t) i)
    (cong₂ _+_ (cong (λ w → zpow w i) up) (cong (λ w → zpow w i) down))

pair-ω₁ : (h t : ℤ) → pow M ∣ (h - (¼ + ½)) →
          (zpow (h + t) +ᴬ zpow t) ≐ √2· (zpow ((⅛ - ¼) + t))
pair-ω₁ h t d i = trans
  (cong (λ u → u + zpow t i) (zpow-cong {h + t} {(- ¼) + t} div i))
  (trans (+-comm (zpow ((- ¼) + t) i) (zpow t i)) (sym split))
  where
  reshape : ∀ h q p t → (h + t) - ((- q) + t) ≡ (h - (q + p)) + ((q + p) + q)
  reshape = solve 4 (λ h q p t →
    (h :+ t) :- ((:- q) :+ t) := (h :- (q :+ p)) :+ ((q :+ p) :+ q)) refl

  regroup : ∀ a b → (a + b) + a ≡ (a + a) + b
  regroup = solve 2 (λ a b → (a :+ b) :+ a := (a :+ a) :+ b) refl

  value : (¼ + ½) + ¼ ≡ pow M
  value = trans (regroup ¼ ½) (trans (cong (λ u → u + ½) ¼+¼) ½+½)

  div : (+ Nᶻ) ∣ ((h + t) - ((- ¼) + t))
  div = Eq.subst ((+ Nᶻ) ∣_)
    (sym (trans (reshape h ¼ ½ t) (cong (λ u → (h - (¼ + ½)) + u) value)))
    (∣m∣n⇒∣m+n d ∣-refl)

  collect : ∀ u q t → u + ((u - q) + t) ≡ ((u + u) - q) + t
  collect = solve 3 (λ u q t →
    u :+ ((u :- q) :+ t) := ((u :+ u) :- q) :+ t) refl

  vanish : ∀ q t → (q - q) + t ≡ t
  vanish = solve 2 (λ q t → (q :- q) :+ t := t) refl

  shift : ∀ u q t → (- u) + ((u - q) + t) ≡ (- q) + t
  shift = solve 3 (λ u q t → (:- u) :+ ((u :- q) :+ t) := (:- q) :+ t) refl

  fst : (+ cᶻ) + ((⅛ - ¼) + t) ≡ t
  fst = trans (collect ⅛ ¼ t)
    (trans (cong (λ w → (w - ¼) + t) ⅛+⅛) (vanish ¼ t))

  snd : (- (+ cᶻ)) + ((⅛ - ¼) + t) ≡ (- ¼) + t
  snd = shift ⅛ ¼ t

  split : √2· (zpow ((⅛ - ¼) + t)) i ≡ zpow t i + zpow ((- ¼) + t) i
  split = trans (√2·-zpow ((⅛ - ¼) + t) i)
    (cong₂ _+_ (cong (λ w → zpow w i) fst) (cong (λ w → zpow w i) snd))


------------------------------------------------------------------------
-- Reading the outputs

-- Outputs with the same values at two paths hit the same states there,
-- whatever the two path-sums.  A Boolean is determined by when it is
-- true.

private
  bool-ext : ∀ {a b : Bool} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) →
             a ≡ b
  bool-ext {true}  {true}  _ _ = refl
  bool-ext {false} {false} _ _ = refl
  bool-ext {true}  {false} f _ = sym (f refl)
  bool-ext {false} {true}  _ g = g refl

hits-eval : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) (x : Assign n)
            (y : Assign m) (y′ : Assign m′) (z : Assign n) →
            (∀ w → eval (out ξ w) x y ≡ eval (out ζ w) x y′) →
            hits ξ x y z ≡ hits ζ x y′ z
hits-eval ξ ζ x y y′ z eq = bool-ext
  (λ h → hits-intro ζ x y′ z (λ w →
           trans (sym (bit≡ w)) (hits-elim ξ x y z h w)))
  (λ h → hits-intro ξ x y z (λ w →
           trans (bit≡ w) (hits-elim ζ x y′ z h w)))
  where
  bit≡ : ∀ w → outBit ξ x y w ≡ outBit ζ x y′ w
  bit≡ w = cong (λ v → not ⌊ (+ 2) ∣? v ⌋) (eq w)


------------------------------------------------------------------------
-- The pair of branches of y₀

-- Denotation's Branches ξ eqf: the summand F x z y is the pair of
-- branches of y₀ over the assignment y to the other path variables,
-- F-form writes it as a guarded ζ^(hd+tv) + ζ^tv, and hitsT is the
-- guard.  Added here: the amplitude as the sum of the pairs, that the
-- summand reads only the values of y, and the four collapses above,
-- each keyed on what hd is modulo 1 at one path.

module Pair {n k m : ℕ} (ξ : PathSum n k (suc m))
            (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w)) where

  open Branches ξ eqf public

  private
    if-cong : ∀ {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
              (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
    if-cong {p = true}  refl a≐b = a≐b
    if-cong {p = false} refl _   = λ _ → refl

    √2·-if : ∀ (p : Bool) (a : Amp) →
             (if p then (√2· a) else 0ᴬ) ≐ √2· (if p then a else 0ᴬ)
    √2·-if true  a _ = refl
    √2·-if false a w = sym (√2·-0ᴬ w)

    ext-cong : ∀ (b : Bool) (y y′ : Assign m) → (∀ j → y j ≡ y′ j) →
               ∀ j → extend b y j ≡ extend b y′ j
    ext-cong b y y′ agree zero    = refl
    ext-cong b y y′ agree (suc j) = agree j

  amp-pairs : ∀ x z → amp ξ x z ≐ Σᴮ (F x z)
  amp-pairs x z i =
    sym (Σᴮ-+ (λ y → Fξ x z (extend true y)) (λ y → Fξ x z (extend false y)) i)

  F-resp : ∀ x z → Respects (F x z)
  F-resp x z y y′ agree w = cong₂ _+_ (br true) (br false)
    where
    br : ∀ b → Fξ x z (extend b y) w ≡ Fξ x z (extend b y′) w
    br b = if-cong
      (hits-≗³ ξ {x} {x} {extend b y} {extend b y′} {z} {z}
               (λ _ → refl) (ext-cong b y y′ agree) (λ _ → refl))
      (λ w′ → cong (λ v → zpow v w′)
        (eval-cong (phase ξ) {x} {x} {extend b y} {extend b y′}
                   (λ _ → refl) (ext-cong b y y′ agree))) w

  F-double : ∀ x z y → pow M ∣ hd x y →
             F x z y ≐ (+ 2) ·ᴬ (if hitsT x y z then zpow (tv x y) else 0ᴬ)
  F-double x z y d w = trans
    (trans (F-form x z y w)
           (if-cong {p = hitsT x y z} refl (pair-double (hd x y) (tv x y) d) w))
    (sym (·ᴬ-if (hitsT x y z) (zpow (tv x y)) w))

  F-cancel : ∀ x z y → pow M ∣ (hd x y - ½) → F x z y ≐ 0ᴬ
  F-cancel x z y d w = trans
    (trans (F-form x z y w)
           (if-cong {p = hitsT x y z} refl (pair-cancel (hd x y) (tv x y) d) w))
    (if-0ᴬ (hitsT x y z) w)

  F-ω₀ : ∀ x z y → pow M ∣ (hd x y - ¼) →
         F x z y ≐ √2· (if hitsT x y z then zpow (⅛ + tv x y) else 0ᴬ)
  F-ω₀ x z y d w = trans
    (trans (F-form x z y w)
           (if-cong {p = hitsT x y z} refl (pair-ω₀ (hd x y) (tv x y) d) w))
    (√2·-if (hitsT x y z) (zpow (⅛ + tv x y)) w)

  F-ω₁ : ∀ x z y → pow M ∣ (hd x y - (¼ + ½)) →
         F x z y ≐ √2· (if hitsT x y z then zpow ((⅛ - ¼) + tv x y) else 0ᴬ)
  F-ω₁ x z y d w = trans
    (trans (F-form x z y w)
           (if-cong {p = hitsT x y z} refl (pair-ω₁ (hd x y) (tv x y) d) w))
    (√2·-if (hitsT x y z) (zpow ((⅛ - ¼) + tv x y)) w)


------------------------------------------------------------------------
-- The four branches of y₀ and y₁

-- With y₀ and y₁ both internal, the four paths over an assignment y to
-- the other path variables hit the same states, and their phases are
-- sums of the quarters of the phase: e₀₀ + y₁e₀₁ + y₀e₁₀ + y₀y₁e₁₁.

module Quad {n k m : ℕ} (ξ : PathSum n k (suc (suc m)))
            (eqf₀ : ∀ w → NoVar (+ 2) y₀ (out ξ w))
            (eqf₁ : ∀ w → NoVar (+ 2) y[ suc zero ] (out ξ w)) where

  -- ξ without y₀, whose first path variable is y₁; and ξ without
  -- either, which has the outputs [Case]'s reduct keeps.

  ξ₁ : PathSum n k (suc m)
  ξ₁ = ⟨ tail-part (phase ξ) , (λ w → tail-part (out ξ w)) ⟩

  ξ₀₀ : PathSum n 0 m
  ξ₀₀ = ⟨ q₀₀ (phase ξ) , (λ w → q₀₀ (out ξ w)) ⟩

  eqf₁′ : ∀ w → NoVar (+ 2) y₀ (out ξ₁ w)
  eqf₁′ w (α , β) y₀∈β = eqf₁ w (α , outside ∷ β) (there y₀∈β)

  e₀₀ e₀₁ e₁₀ e₁₁ : Assign n → Assign m → ℤ
  e₀₀ x y = eval (q₀₀ (phase ξ)) x y
  e₀₁ x y = eval (q₀₁ (phase ξ)) x y
  e₁₀ x y = eval (q₁₀ (phase ξ)) x y
  e₁₁ x y = eval (q₁₁ (phase ξ)) x y

  hitsQ : Assign n → Assign m → Assign n → Bool
  hitsQ x y z = hits ξ₀₀ x y z

  Fξ : Assign n → Assign n → Assign (suc (suc m)) → Amp
  Fξ x z y′ = if hits ξ x y′ z then zpow (eval (phase ξ) x y′) else 0ᴬ

  -- The four branches, in the order the sum over assignments visits
  -- them: y₀ first.

  Fq : Assign n → Assign n → Assign m → Amp
  Fq x z y =
    (Fξ x z (extend true  (extend true y)) +ᴬ
     Fξ x z (extend true  (extend false y))) +ᴬ
    (Fξ x z (extend false (extend true y)) +ᴬ
     Fξ x z (extend false (extend false y)))

  amp-quads : ∀ x z → amp ξ x z ≐ Σᴮ (Fq x z)
  amp-quads x z i = sym (trans (Σᴮ-+ A B i)
    (cong₂ _+_ (Σᴮ-+ a₁ a₀ i) (Σᴮ-+ b₁ b₀ i)))
    where
    a₁ a₀ b₁ b₀ A B : Assign m → Amp
    a₁ y = Fξ x z (extend true (extend true y))
    a₀ y = Fξ x z (extend true (extend false y))
    b₁ y = Fξ x z (extend false (extend true y))
    b₀ y = Fξ x z (extend false (extend false y))
    A y = a₁ y +ᴬ a₀ y
    B y = b₁ y +ᴬ b₀ y

  private
    if-cong : ∀ {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
              (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
    if-cong {p = true}  refl a≐b = a≐b
    if-cong {p = false} refl _   = λ _ → refl

    if-quad : ∀ (p : Bool) (a b c d : Amp) →
              (((if p then a else 0ᴬ) +ᴬ (if p then b else 0ᴬ)) +ᴬ
               ((if p then c else 0ᴬ) +ᴬ (if p then d else 0ᴬ)))
              ≐ (if p then ((a +ᴬ b) +ᴬ (c +ᴬ d)) else 0ᴬ)
    if-quad true  a b c d _ = refl
    if-quad false a b c d _ = refl

  -- All four paths hit what the path-sum without y₀ and y₁ hits.

  hits-quad : ∀ (b₀ b₁ : Bool) x z (y : Assign m) →
              hits ξ x (extend b₀ (extend b₁ y)) z ≡ hitsQ x y z
  hits-quad b₀ b₁ x z y = trans (same-hits ξ eqf₀ b₀ x z (extend b₁ y))
                                (same-hits ξ₁ eqf₁′ b₁ x z y)

  -- And their phases are sums of quarters.

  phase₁₁ : ∀ x y → eval (phase ξ) x (extend true (extend true y)) ≡
                    (e₁₁ x y + e₁₀ x y) + (e₀₁ x y + e₀₀ x y)
  phase₁₁ x y = trans (eval-true (phase ξ) x (extend true y))
    (cong₂ _+_ (eval-true (head-part (phase ξ)) x y)
               (eval-true (tail-part (phase ξ)) x y))

  phase₁₀ : ∀ x y → eval (phase ξ) x (extend true (extend false y)) ≡
                    e₁₀ x y + e₀₀ x y
  phase₁₀ x y = trans (eval-true (phase ξ) x (extend false y))
    (cong₂ _+_ (eval-false (head-part (phase ξ)) x y)
               (eval-false (tail-part (phase ξ)) x y))

  phase₀₁ : ∀ x y → eval (phase ξ) x (extend false (extend true y)) ≡
                    e₀₁ x y + e₀₀ x y
  phase₀₁ x y = trans (eval-false (phase ξ) x (extend true y))
    (eval-true (tail-part (phase ξ)) x y)

  phase₀₀ : ∀ x y → eval (phase ξ) x (extend false (extend false y)) ≡
                    e₀₀ x y
  phase₀₀ x y = trans (eval-false (phase ξ) x (extend false y))
    (eval-false (tail-part (phase ξ)) x y)

  Fq-form : ∀ x z y → Fq x z y ≐
            (if hitsQ x y z
             then ((zpow ((e₁₁ x y + e₁₀ x y) + (e₀₁ x y + e₀₀ x y)) +ᴬ
                    zpow (e₁₀ x y + e₀₀ x y)) +ᴬ
                   (zpow (e₀₁ x y + e₀₀ x y) +ᴬ zpow (e₀₀ x y)))
             else 0ᴬ)
  Fq-form x z y i = trans
    (cong₂ _+_ (cong₂ _+_ (branch true true (phase₁₁ x y) i)
                          (branch true false (phase₁₀ x y) i))
               (cong₂ _+_ (branch false true (phase₀₁ x y) i)
                          (branch false false (phase₀₀ x y) i)))
    (if-quad (hitsQ x y z)
      (zpow ((e₁₁ x y + e₁₀ x y) + (e₀₁ x y + e₀₀ x y)))
      (zpow (e₁₀ x y + e₀₀ x y)) (zpow (e₀₁ x y + e₀₀ x y)) (zpow (e₀₀ x y)) i)
    where
    branch : ∀ (b₀ b₁ : Bool) {e : ℤ} →
             eval (phase ξ) x (extend b₀ (extend b₁ y)) ≡ e →
             Fξ x z (extend b₀ (extend b₁ y)) ≐
             (if hitsQ x y z then zpow e else 0ᴬ)
    branch b₀ b₁ eq = if-cong (hits-quad b₀ b₁ x z y)
                              (λ j → cong (λ u → zpow u j) eq)


------------------------------------------------------------------------
-- Four branches with the y₀y₁ coefficient ½

-- a is the phase without y₀ and y₁, h and v the coefficients of y₀ and
-- of y₁, d that of y₀y₁.  With d ≡ ½ the sum is
-- ζ^a (1 + ζ^h + ζ^v - ζ^(h+v)): when X = 0 the coefficient h is ½Q,
-- and the sum is 2ζ^a or 2ζ^(a+v) as Q is 0 or 1; when X = 1 it is v
-- that is ½Q′, and the sum is 2ζ^a or 2ζ^(a+h).  Either way it is twice
-- the power of ζ at (1 - X)(a + Qv) + X(a + Q′h), the reduct's phase.

private
  -- The two premises in each case, simplified.

  at00 : ∀ h u w → h - ((u * 0ℤ) + (w * 0ℤ)) ≡ h
  at00 = solve 3 (λ h u w → h :- ((u :* con 0ℤ) :+ (w :* con 0ℤ)) := h) refl

  at01 : ∀ h u w → h - ((u * 0ℤ) + (w * 1ℤ)) ≡ h - w
  at01 = solve 3 (λ h u w →
    h :- ((u :* con 0ℤ) :+ (w :* con 1ℤ)) := h :- w) refl

  at10 : ∀ v u w → v - ((u * (1ℤ - 1ℤ)) + (w * 0ℤ)) ≡ v
  at10 = solve 3 (λ v u w →
    v :- ((u :* (con 1ℤ :- con 1ℤ)) :+ (w :* con 0ℤ)) := v) refl

  at11 : ∀ v u w → v - ((u * (1ℤ - 1ℤ)) + (w * 1ℤ)) ≡ v - w
  at11 = solve 3 (λ v u w →
    v :- ((u :* (con 1ℤ :- con 1ℤ)) :+ (w :* con 1ℤ)) := v :- w) refl

  -- Exponents of ζ that differ by a multiple of 2^M, or by ½.

  neg-of : ∀ {D} e e′ → pow M ∣ D → e - (e′ + ½) ≡ D →
           zpow e ≐ -ᴬ (zpow e′)
  neg-of e e′ d eq i = trans (by-∣ e (e′ + (+ Hᶻ)) d eq i) (zpow-anti e′ i)

  two-halves : ∀ {D E} → pow M ∣ D → pow M ∣ E → pow M ∣ ((D + E) + (½ + ½))
  two-halves d e =
    ∣m∣n⇒∣m+n (∣m∣n⇒∣m+n d e) (Eq.subst (pow M ∣_) (sym ½+½) ∣-refl)

  -- The four collapses.

  quad₀₀ : ∀ a h v d → pow M ∣ (d - ½) → pow M ∣ h →
           ((zpow ((d + h) + (v + a)) +ᴬ zpow (h + a)) +ᴬ
            (zpow (v + a) +ᴬ zpow a)) ≐ (+ 2) ·ᴬ zpow a
  quad₀₀ a h v d dd dh i = trans
    (cong₂ _+_
      (cong₂ _+_ (neg-of ((d + h) + (v + a)) (v + a) dd' (e₁ d h v a ½) i)
                 (by-∣ (h + a) a dh (e₂ h a) i))
      refl)
    (sum (zpow (v + a) i) (zpow a i))
    where
    dd' : pow M ∣ ((d - ½) + h)
    dd' = ∣m∣n⇒∣m+n dd dh
    e₁ : ∀ d h v a t → ((d + h) + (v + a)) - ((v + a) + t) ≡ (d - t) + h
    e₁ = solve 5 (λ d h v a t →
      ((d :+ h) :+ (v :+ a)) :- ((v :+ a) :+ t) := (d :- t) :+ h) refl
    e₂ : ∀ h a → (h + a) - a ≡ h
    e₂ = solve 2 (λ h a → (h :+ a) :- a := h) refl
    sum : ∀ p t → ((- p) + t) + (p + t) ≡ (+ 2) * t
    sum = solve 2 (λ p t → ((:- p) :+ t) :+ (p :+ t) := con (+ 2) :* t) refl

  quad₀₁ : ∀ a h v d → pow M ∣ (d - ½) → pow M ∣ (h - ½) →
           ((zpow ((d + h) + (v + a)) +ᴬ zpow (h + a)) +ᴬ
            (zpow (v + a) +ᴬ zpow a)) ≐ (+ 2) ·ᴬ zpow (v + a)
  quad₀₁ a h v d dd dh i = trans
    (cong₂ _+_ (cong₂ _+_ (by-∣ ((d + h) + (v + a)) (v + a) (two-halves dd dh)
                                (e₁ d h v a ½) i)
                          (neg-of (h + a) a dh (e₂ h a ½) i))
               refl)
    (sum (zpow (v + a) i) (zpow a i))
    where
    e₁ : ∀ d h v a t →
         ((d + h) + (v + a)) - (v + a) ≡ ((d - t) + (h - t)) + (t + t)
    e₁ = solve 5 (λ d h v a t →
      ((d :+ h) :+ (v :+ a)) :- (v :+ a) := ((d :- t) :+ (h :- t)) :+ (t :+ t))
      refl
    e₂ : ∀ h a t → (h + a) - (a + t) ≡ h - t
    e₂ = solve 3 (λ h a t → (h :+ a) :- (a :+ t) := h :- t) refl
    sum : ∀ p t → (p + (- t)) + (p + t) ≡ (+ 2) * p
    sum = solve 2 (λ p t → (p :+ (:- t)) :+ (p :+ t) := con (+ 2) :* p) refl

  quad₁₀ : ∀ a h v d → pow M ∣ (d - ½) → pow M ∣ v →
           ((zpow ((d + h) + (v + a)) +ᴬ zpow (h + a)) +ᴬ
            (zpow (v + a) +ᴬ zpow a)) ≐ (+ 2) ·ᴬ zpow a
  quad₁₀ a h v d dd dv i = trans
    (cong₂ _+_
      (cong₂ _+_ (neg-of ((d + h) + (v + a)) (h + a) dd' (e₁ d h v a ½) i)
                 refl)
      (cong₂ _+_ (by-∣ (v + a) a dv (e₂ v a) i) refl))
    (sum (zpow (h + a) i) (zpow a i))
    where
    dd' : pow M ∣ ((d - ½) + v)
    dd' = ∣m∣n⇒∣m+n dd dv
    e₁ : ∀ d h v a t → ((d + h) + (v + a)) - ((h + a) + t) ≡ (d - t) + v
    e₁ = solve 5 (λ d h v a t →
      ((d :+ h) :+ (v :+ a)) :- ((h :+ a) :+ t) := (d :- t) :+ v) refl
    e₂ : ∀ v a → (v + a) - a ≡ v
    e₂ = solve 2 (λ v a → (v :+ a) :- a := v) refl
    sum : ∀ p t → ((- p) + p) + (t + t) ≡ (+ 2) * t
    sum = solve 2 (λ p t → ((:- p) :+ p) :+ (t :+ t) := con (+ 2) :* t) refl

  quad₁₁ : ∀ a h v d → pow M ∣ (d - ½) → pow M ∣ (v - ½) →
           ((zpow ((d + h) + (v + a)) +ᴬ zpow (h + a)) +ᴬ
            (zpow (v + a) +ᴬ zpow a)) ≐ (+ 2) ·ᴬ zpow (h + a)
  quad₁₁ a h v d dd dv i = trans
    (cong₂ _+_ (cong₂ _+_ (by-∣ ((d + h) + (v + a)) (h + a) (two-halves dd dv)
                                (e₁ d h v a ½) i)
                          refl)
               (cong₂ _+_ (neg-of (v + a) a dv (e₂ v a ½) i) refl))
    (sum (zpow (h + a) i) (zpow a i))
    where
    e₁ : ∀ d h v a t →
         ((d + h) + (v + a)) - (h + a) ≡ ((d - t) + (v - t)) + (t + t)
    e₁ = solve 5 (λ d h v a t →
      ((d :+ h) :+ (v :+ a)) :- (h :+ a) := ((d :- t) :+ (v :- t)) :+ (t :+ t))
      refl
    e₂ : ∀ v a t → (v + a) - (a + t) ≡ v - t
    e₂ = solve 3 (λ v a t → (v :+ a) :- (a :+ t) := v :- t) refl
    sum : ∀ p t → (p + p) + ((- t) + t) ≡ (+ 2) * p
    sum = solve 2 (λ p t → (p :+ p) :+ ((:- t) :+ t) := con (+ 2) :* p) refl

  -- Twice a power of ζ at an exponent known by an equation.
  twice-at : ∀ {e e′} → e ≡ e′ → (+ 2) ·ᴬ zpow e ≐ (+ 2) ·ᴬ zpow e′
  twice-at eq i = cong (λ u → (+ 2) * zpow u i) eq

quad : (a h v d xv qv q′v : ℤ) → IsBit xv → IsBit qv → IsBit q′v →
       pow M ∣ (d - ½) →
       pow M ∣ (h - ((¼ * xv) + (½ * qv))) →
       pow M ∣ (v - ((¼ * (1ℤ - xv)) + (½ * q′v))) →
       ((zpow ((d + h) + (v + a)) +ᴬ zpow (h + a)) +ᴬ (zpow (v + a) +ᴬ zpow a))
       ≐ (+ 2) ·ᴬ zpow (((1ℤ - xv) * (a + (qv * v))) + (xv * (a + (q′v * h))))
quad a h v d xv qv q′v (inj₁ refl) (inj₁ refl) _ dd dh _ i = trans
  (quad₀₀ a h v d dd (Eq.subst (pow M ∣_) (at00 h ¼ ½) dh) i)
  (twice-at (sym (E a h v q′v)) i)
  where
  E : ∀ a h v q → ((1ℤ - 0ℤ) * (a + (0ℤ * v))) + (0ℤ * (a + (q * h))) ≡ a
  E = solve 4 (λ a h v q →
    ((con 1ℤ :- con 0ℤ) :* (a :+ (con 0ℤ :* v))) :+ (con 0ℤ :* (a :+ (q :* h)))
    := a) refl
quad a h v d xv qv q′v (inj₁ refl) (inj₂ refl) _ dd dh _ i = trans
  (quad₀₁ a h v d dd (Eq.subst (pow M ∣_) (at01 h ¼ ½) dh) i)
  (twice-at (sym (E a h v q′v)) i)
  where
  E : ∀ a h v q → ((1ℤ - 0ℤ) * (a + (1ℤ * v))) + (0ℤ * (a + (q * h))) ≡ v + a
  E = solve 4 (λ a h v q →
    ((con 1ℤ :- con 0ℤ) :* (a :+ (con 1ℤ :* v))) :+ (con 0ℤ :* (a :+ (q :* h)))
    := v :+ a) refl
quad a h v d xv qv q′v (inj₂ refl) _ (inj₁ refl) dd _ dv i = trans
  (quad₁₀ a h v d dd (Eq.subst (pow M ∣_) (at10 v ¼ ½) dv) i)
  (twice-at (sym (E a h v qv)) i)
  where
  E : ∀ a h v q → ((1ℤ - 1ℤ) * (a + (q * v))) + (1ℤ * (a + (0ℤ * h))) ≡ a
  E = solve 4 (λ a h v q →
    ((con 1ℤ :- con 1ℤ) :* (a :+ (q :* v))) :+ (con 1ℤ :* (a :+ (con 0ℤ :* h)))
    := a) refl
quad a h v d xv qv q′v (inj₂ refl) _ (inj₂ refl) dd _ dv i = trans
  (quad₁₁ a h v d dd (Eq.subst (pow M ∣_) (at11 v ¼ ½) dv) i)
  (twice-at (sym (E a h v qv)) i)
  where
  E : ∀ a h v q → ((1ℤ - 1ℤ) * (a + (q * v))) + (1ℤ * (a + (1ℤ * h))) ≡ h + a
  E = solve 4 (λ a h v q →
    ((con 1ℤ :- con 1ℤ) :* (a :+ (q :* v))) :+ (con 1ℤ :* (a :+ (con 1ℤ :* h)))
    := h :+ a) refl
