------------------------------------------------------------------------
-- Presentations of groups
--
-- Reading the quotients of figure 2 off the phase
--
-- Three rules of figure 2 (Amy, QPL 2018) quantify over quotients:
-- [ω] applies when *some* Boolean-valued Q makes the quotient of the
-- phase by y₀ equal to ¼ + ½Q; [HH] when some Q free of y_i makes it
-- ½(y_i + Q); [Case] when some X, Q and Q′ decompose the phase twice.
-- Deciding whether a rule applies (PathSum.Full.Match) therefore needs
-- a quotient to be found, not guessed.  This module computes, from
-- the coefficients of the phase, one canonical candidate per rule, and
-- proves it complete: whenever any quotient works, the canonical one
-- does.
--
-- The reason is that the premises see a quotient only through one
-- binary digit of each coefficient.  Since 2·½ is a multiple of 2^M,
-- the term ½·q is determined modulo 2^M by the parity of q.  So the
-- congruence A ≡ B + ½·Q (mod 2^M), coefficient by coefficient, holds
-- for some polynomial Q exactly when it holds for the polynomial of
-- digits (digitᴾ: 1 at γ when A γ ≡ B γ + ½, else 0; digit-≈), and
-- then for every polynomial with the same parities as the digits, in
-- particular for their Boolean-valued lift liftᴮ (lemma 2.5; lift-≈).
-- The candidate is that lift (readᴾ).  The completeness lemmas below
-- assume nothing of the quotient they start from, so the side
-- condition "Q is Boolean-valued" never prevents a rule from applying:
-- a rule applies with some integer quotient iff it applies with a
-- Boolean-valued one, its candidate.  (When M ≥ 1 the candidate is
-- also the only Boolean-valued quotient that works -- two that work
-- have the same parities, and lift-unique -- but the matcher does not
-- need that, and it is not stated here.)
--
-- Rule by rule:
--
-- * [ω]: the ½-digits of the head part against ¼ (ωQuot).
-- * [HH]: the quotient must moreover be free of y_i.  The digits are
--   masked at the monomials containing y_i (maskᴾ), where a quotient
--   free of y_i has coefficient 0 anyway, and a lift of a polynomial
--   free of y_i modulo 2 is free of it exactly (Absent-liftᴮ; hhQuot).
-- * [Case]: X enters with weight ¼.  Modulo ½ the premise on q₁₀
--   reads q₁₀ ≡ ¼X, and ½ divides 2·¼, so X is read off as a digit
--   one place further down (caseX) and Q, Q′ as the ½-digits of what
--   is left (caseQ, caseQ′).  The premise on q₀₁ need not be consulted
--   to find X: two X both satisfying q₁₀'s congruence modulo ½ differ
--   by a multiple of ½ once scaled by ¼, so q₀₁'s congruence for one
--   gives it for the other (case-complete).
--
-- The arithmetic uses only 2^M ∣ 2·½, ½ ∣ 2·¼ and ½ ∣ 2^M (pow∣½·2,
-- ½∣¼·2, ½∣pow), which hold at every M -- also at M ≤ 1, where the
-- constants of PathSum.Reduction collapse to 1 -- so nothing here
-- assumes M ≥ 3.  Nothing here is about path-sums either: the rules'
-- premises are instances at the parts of the phase they name.  The
-- search is not efficient -- a lift ⊕-folds over all 2^(n+m) monomials
-- -- and the paper's polynomial-time matching is not formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Full.Canonical (M : ℕ) where

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; quotient; ∣-refl; ∣-trans; ∣-reflexive;
   ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣m⇒∣m*n)
open import Data.Integer.Properties using
  (+-identityˡ; *-identityʳ; *-distribˡ-+)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _∸_)
open import Data.Nat.Properties using (m∸n≤m; ∸-+-assoc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Order M using (pow; pow-∣; pow-suc; parity)
open import PathSum.Polynomial using
  (Mon; Poly; Var; _∈ᵐ_; _∈ᵐ?_; _≟ᵐ_; 0ᴾ; κ; μ; _+ᴾ_; _-ᴾ_; _·ᴾ_;
   _≈[_]_; NoVar)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Polynomial.Product using (monoᴾ)
open import PathSum.Polynomial.Boolean using
  (BoolValued; ⨁sub; liftᴮ; BoolValued-liftᴮ; liftᴮ-≈; Absent-⊕ᴾ)
open import PathSum.Polynomial.Substitution using (Absent)
open import PathSum.Reduction M using (¼; ½)

import Data.Integer.Divisibility.Signed as Div

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The dyadic digits

-- Doubling ½ gives a multiple of 2^M, and doubling ¼ a multiple of ½,
-- at every M; and ½ divides 2^M.

private
  pow-half : ∀ e → pow e ∣ (pow (e ∸ 1) * (+ 2))
  pow-half zero    =
    divides (pow 0 * (+ 2)) (sym (*-identityʳ (pow 0 * (+ 2))))
  pow-half (suc e) = ∣-reflexive (pow-suc e)

pow∣½·2 : pow M ∣ (½ * (+ 2))
pow∣½·2 = pow-half M

½∣¼·2 : ½ ∣ (¼ * (+ 2))
½∣¼·2 = subst (λ t → ½ ∣ (pow t * (+ 2))) (∸-+-assoc M 1 1)
              (pow-half (M ∸ 1))

½∣pow : ½ ∣ pow M
½∣pow = pow-∣ (m∸n≤m M 1)


------------------------------------------------------------------------
-- One binary digit

-- digit d h a b is 1 when a ≡ b + h (mod d), and 0 otherwise.  When d
-- divides 2h, whether a ≡ b + h·q (mod d) depends on q only through
-- its parity, and if some q works, the digit does.

digit : ℤ → ℤ → ℤ → ℤ → ℤ
digit d h a b = if ⌊ d ∣? (a - (b + h * 1ℤ)) ⌋ then 1ℤ else 0ℤ

private
  even-shape : ∀ a b h r →
               a - (b + h * 0ℤ) ≡
               (a - (b + h * (r * (+ 2)))) + ((h * (+ 2)) * r)
  even-shape = solve 4 (λ a b h r →
    a :- (b :+ h :* con 0ℤ) :=
    (a :- (b :+ h :* (r :* con (+ 2)))) :+ ((h :* con (+ 2)) :* r)) refl

  odd-shape : ∀ a b h r →
              a - (b + h * 1ℤ) ≡
              (a - (b + h * ((r * (+ 2)) + 1ℤ))) + ((h * (+ 2)) * r)
  odd-shape = solve 4 (λ a b h r →
    a :- (b :+ h :* con 1ℤ) :=
    (a :- (b :+ h :* ((r :* con (+ 2)) :+ con 1ℤ))) :+
    ((h :* con (+ 2)) :* r)) refl

  shift-shape : ∀ a b h u u′ →
                a - (b + h * u′) ≡ (a - (b + h * u)) - (h * (u′ - u))
  shift-shape = solve 5 (λ a b h u u′ →
    a :- (b :+ h :* u′) := (a :- (b :+ h :* u)) :- (h :* (u′ :- u))) refl

  swap-shape : ∀ h r → (h * (+ 2)) * r ≡ h * (r * (+ 2))
  swap-shape = solve 2 (λ h r →
    (h :* con (+ 2)) :* r := h :* (r :* con (+ 2))) refl

digit-complete : ∀ {d} h a b q → d ∣ (h * (+ 2)) →
                 d ∣ (a - (b + h * q)) → d ∣ (a - (b + h * digit d h a b))
digit-complete {d} h a b q d∣2h hq = go (d ∣? (a - (b + h * 1ℤ)))
  where
  hq′ : ∀ {z} → q ≡ z → d ∣ (a - (b + h * z))
  hq′ q≡ = subst (λ z → d ∣ (a - (b + h * z))) q≡ hq

  go : (t : Dec (d ∣ (a - (b + h * 1ℤ)))) →
       d ∣ (a - (b + h * (if ⌊ t ⌋ then 1ℤ else 0ℤ)))
  go (yes one) = one
  go (no ¬one) with parity q
  ... | inj₁ (r , q≡) = subst (d ∣_) (sym (even-shape a b h r))
          (∣m∣n⇒∣m+n (hq′ q≡) (∣m⇒∣m*n r d∣2h))
  ... | inj₂ (r , q≡) = contradiction
          (subst (d ∣_) (sym (odd-shape a b h r))
            (∣m∣n⇒∣m+n (hq′ q≡) (∣m⇒∣m*n r d∣2h)))
          ¬one

-- And any value of the same parity will do as well.

digit-shift : ∀ {d} h a b u u′ → d ∣ (h * (+ 2)) →
              d ∣ (a - (b + h * u)) → (+ 2) ∣ (u′ - u) →
              d ∣ (a - (b + h * u′))
digit-shift {d} h a b u u′ d∣2h hu (divides r eq) =
  subst (d ∣_) (sym (shift-shape a b h u u′))
    (∣m∣n⇒∣m-n hu
      (subst (λ z → d ∣ (h * z)) (sym eq)
        (subst (d ∣_) (swap-shape h r) (∣m⇒∣m*n r d∣2h))))


------------------------------------------------------------------------
-- Digits of a polynomial, and their lift

-- The congruence A ≡ B + h·Q (mod d), coefficient by coefficient, for
-- some Q gives it for the digits, and then for their Boolean-valued
-- lift, whose coefficients have the digits' parities (lemma 2.5).

digitᴾ : ℤ → ℤ → Poly n m → Poly n m → Poly n m
digitᴾ d h A B γ = digit d h (A γ) (B γ)

digit-≈ : ∀ {d} h (A B Q : Poly n m) → d ∣ (h * (+ 2)) →
          A ≈[ d ] (B +ᴾ (h ·ᴾ Q)) →
          A ≈[ d ] (B +ᴾ (h ·ᴾ digitᴾ d h A B))
digit-≈ h A B Q d∣2h eq γ = digit-complete h (A γ) (B γ) (Q γ) d∣2h (eq γ)

lift-≈ : ∀ {d} h (A B f : Poly n m) → d ∣ (h * (+ 2)) →
         A ≈[ d ] (B +ᴾ (h ·ᴾ f)) → A ≈[ d ] (B +ᴾ (h ·ᴾ liftᴮ f))
lift-≈ h A B f d∣2h eq γ =
  digit-shift h (A γ) (B γ) (f γ) (liftᴮ f γ) d∣2h (eq γ) (liftᴮ-≈ f γ)

-- The canonical quotient.

readᴾ : ℤ → ℤ → Poly n m → Poly n m → Poly n m
readᴾ d h A B = liftᴮ (digitᴾ d h A B)

BoolValued-readᴾ : ∀ d h (A B : Poly n m) → BoolValued (readᴾ d h A B)
BoolValued-readᴾ d h A B = BoolValued-liftᴮ (digitᴾ d h A B)

read-≈ : ∀ {d} h (A B Q : Poly n m) → d ∣ (h * (+ 2)) →
         A ≈[ d ] (B +ᴾ (h ·ᴾ Q)) →
         A ≈[ d ] (B +ᴾ (h ·ᴾ readᴾ d h A B))
read-≈ {d = d} h A B Q d∣2h eq =
  lift-≈ h A B (digitᴾ d h A B) d∣2h (digit-≈ h A B Q d∣2h eq)


------------------------------------------------------------------------
-- Quotients free of a variable

-- The digits with every monomial containing v set to 0.

maskᴾ : Var n m → Poly n m → Poly n m
maskᴾ v P γ = if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ

NoVar-maskᴾ : ∀ {c} (v : Var n m) (P : Poly n m) → NoVar c v (maskᴾ v P)
NoVar-maskᴾ {c = c} v P γ v∈γ = go (v ∈ᵐ? γ)
  where
  go : (t : Dec (v ∈ᵐ γ)) → c ∣ (if ⌊ t ⌋ then 0ℤ else P γ)
  go (yes _)   = i∣0
  go (no v∉γ) = contradiction v∈γ v∉γ

-- A quotient free of v has coefficient 0 where the mask is, so the
-- masked digits work whenever such a quotient does.

mask-≈ : ∀ {d} h (v : Var n m) (A B Q : Poly n m) → d ∣ (h * (+ 2)) →
         Absent v Q → A ≈[ d ] (B +ᴾ (h ·ᴾ Q)) →
         A ≈[ d ] (B +ᴾ (h ·ᴾ maskᴾ v (digitᴾ d h A B)))
mask-≈ {d = d} h v A B Q d∣2h absQ eq γ = go (v ∈ᵐ? γ)
  where
  go : (t : Dec (v ∈ᵐ γ)) →
       d ∣ (A γ - (B γ + h * (if ⌊ t ⌋ then 0ℤ
                                 else digit d h (A γ) (B γ))))
  go (yes v∈γ) =
    subst (λ z → d ∣ (A γ - (B γ + h * z))) (absQ γ v∈γ) (eq γ)
  go (no _)    = digit-≈ h A B Q d∣2h eq γ

-- The lift of a polynomial free of v modulo 2 is free of v exactly: it
-- folds ⊕ over the monomials with odd coefficient, none containing v.

Absent-monoᴾ : (v : Var n m) (γ₀ : Mon n m) → ¬ (v ∈ᵐ γ₀) →
               Absent v (monoᴾ γ₀)
Absent-monoᴾ v γ₀ v∉γ₀ γ v∈γ with γ ≟ᵐ γ₀
... | yes refl = contradiction v∈γ v∉γ₀
... | no  _    = refl

Absent-⨁sub : ∀ {j} (v : Var n m) (F : Subset j → Poly n m) →
              (∀ s → Absent v (F s)) → Absent v (⨁sub F)
Absent-⨁sub {j = zero}  v F h = h []
Absent-⨁sub {j = suc j} v F h =
  Absent-⊕ᴾ {v = v} {A = ⨁sub (λ s → F (inside ∷ s))}
             {B = ⨁sub (λ s → F (outside ∷ s))}
    (Absent-⨁sub v (λ s → F (inside ∷ s)) (λ s → h (inside ∷ s)))
    (Absent-⨁sub v (λ s → F (outside ∷ s)) (λ s → h (outside ∷ s)))

Absent-liftᴮ : (v : Var n m) (f : Poly n m) → NoVar (+ 2) v f →
               Absent v (liftᴮ f)
Absent-liftᴮ {n} {m} v f nv =
  Absent-⨁sub v (λ α → ⨁sub (λ β → G (α , β))) (λ α →
    Absent-⨁sub v (λ β → G (α , β)) (λ β →
      pick (α , β) ((+ 2) ∣? f (α , β))))
  where
  G : Mon n m → Poly n m
  G γ = if ⌊ (+ 2) ∣? f γ ⌋ then 0ᴾ else monoᴾ γ

  pick : ∀ γ (t : Dec ((+ 2) ∣ f γ)) →
         Absent v (if ⌊ t ⌋ then 0ᴾ else monoᴾ γ)
  pick γ (yes _)  = λ _ _ → refl
  pick γ (no ¬2∣) = Absent-monoᴾ v γ (λ v∈γ → ¬2∣ (nv γ v∈γ))


------------------------------------------------------------------------
-- Rearranging a congruence

-- h·(U + Q) is h·U + h·Q, coefficient by coefficient.

split-≈ : ∀ {d} h (A U Q : Poly n m) →
          A ≈[ d ] (h ·ᴾ (U +ᴾ Q)) → A ≈[ d ] ((h ·ᴾ U) +ᴾ (h ·ᴾ Q))
split-≈ {d = d} h A U Q eq γ =
  subst (λ z → d ∣ (A γ - z)) (*-distribˡ-+ h (U γ) (Q γ)) (eq γ)

unsplit-≈ : ∀ {d} h (A U Q : Poly n m) →
            A ≈[ d ] ((h ·ᴾ U) +ᴾ (h ·ᴾ Q)) → A ≈[ d ] (h ·ᴾ (U +ᴾ Q))
unsplit-≈ {d = d} h A U Q eq γ =
  subst (λ z → d ∣ (A γ - z)) (sym (*-distribˡ-+ h (U γ) (Q γ))) (eq γ)

-- Adding 0ᴾ in front, and taking it away.

to-0 : ∀ {d} (A C : Poly n m) → A ≈[ d ] C → A ≈[ d ] (0ᴾ +ᴾ C)
to-0 {d = d} A C eq γ =
  subst (λ z → d ∣ (A γ - z)) (sym (+-identityˡ (C γ))) (eq γ)

from-0 : ∀ {d} (A C : Poly n m) → A ≈[ d ] (0ᴾ +ᴾ C) → A ≈[ d ] C
from-0 {d = d} A C eq γ =
  subst (λ z → d ∣ (A γ - z)) (+-identityˡ (C γ)) (eq γ)

-- Modulo a divisor d′ of d, a term h·Q with d′ ∣ h vanishes.

private
  coarse-shape : ∀ a b h q → a - b ≡ (a - (b + h * q)) + h * q
  coarse-shape = solve 4 (λ a b h q →
    a :- b := (a :- (b :+ h :* q)) :+ h :* q) refl

coarsen : ∀ {d d′} h (A B Q : Poly n m) → d′ ∣ d → d′ ∣ h →
          A ≈[ d ] (B +ᴾ (h ·ᴾ Q)) → A ≈[ d′ ] B
coarsen {d′ = d′} h A B Q d′∣d d′∣h eq γ =
  subst (d′ ∣_) (sym (coarse-shape (A γ) (B γ) h (Q γ)))
    (∣m∣n⇒∣m+n (∣-trans d′∣d (eq γ)) (∣m⇒∣m*n (Q γ) d′∣h))

-- Conversely, a congruence modulo h is one modulo anything once h
-- times the quotients is added.

private
  refine-shape : ∀ a c h t → a - (c + h * t) ≡ (a - c) - h * t
  refine-shape = solve 4 (λ a c h t →
    a :- (c :+ h :* t) := (a :- c) :- h :* t) refl

  cancel-shape : ∀ h t → t * h - h * t ≡ 0ℤ
  cancel-shape = solve 2 (λ h t → t :* h :- h :* t := con 0ℤ) refl

refine : ∀ {d h} (A C : Poly n m) → A ≈[ h ] C →
         Σ (Poly n m) (λ t → A ≈[ d ] (C +ᴾ (h ·ᴾ t)))
refine {d = d} {h = h} A C eq = t , λ γ → subst (d ∣_) (sym (exact γ)) i∣0
  where
  t : Poly _ _
  t γ = quotient (eq γ)

  exact : ∀ γ → A γ - (C γ + h * t γ) ≡ 0ℤ
  exact γ = trans (refine-shape (A γ) (C γ) h (t γ))
    (trans (cong (_- h * t γ) (Div._∣_.equality (eq γ)))
           (cancel-shape h (t γ)))


------------------------------------------------------------------------
-- [ω]: ¼ + ½Q

ωQuot : Poly n m → Poly n m
ωQuot H = readᴾ (pow M) ½ H (κ ¼)

BoolValued-ωQuot : (H : Poly n m) → BoolValued (ωQuot H)
BoolValued-ωQuot H = BoolValued-readᴾ (pow M) ½ H (κ ¼)

ωQuot-complete : (H Q : Poly n m) → H ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q)) →
                 H ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ ωQuot H))
ωQuot-complete H Q = read-≈ ½ H (κ ¼) Q pow∣½·2


------------------------------------------------------------------------
-- [HH]: ½(v + Q), with Q free of v

hhQuot : Var n m → Poly n m → Poly n m
hhQuot v H = liftᴮ (maskᴾ v (digitᴾ (pow M) ½ H (½ ·ᴾ μ v)))

BoolValued-hhQuot : (v : Var n m) (H : Poly n m) → BoolValued (hhQuot v H)
BoolValued-hhQuot v H =
  BoolValued-liftᴮ (maskᴾ v (digitᴾ (pow M) ½ H (½ ·ᴾ μ v)))

Absent-hhQuot : (v : Var n m) (H : Poly n m) → Absent v (hhQuot v H)
Absent-hhQuot v H = Absent-liftᴮ v (maskᴾ v (digitᴾ (pow M) ½ H (½ ·ᴾ μ v)))
  (NoVar-maskᴾ v (digitᴾ (pow M) ½ H (½ ·ᴾ μ v)))

hhQuot-complete : (v : Var n m) (H Q : Poly n m) → Absent v Q →
                  H ≈[ pow M ] (½ ·ᴾ (μ v +ᴾ Q)) →
                  H ≈[ pow M ] (½ ·ᴾ (μ v +ᴾ hhQuot v H))
hhQuot-complete v H Q absQ eq = unsplit-≈ ½ H (μ v) (hhQuot v H)
  (lift-≈ ½ H (½ ·ᴾ μ v) (maskᴾ v (digitᴾ (pow M) ½ H (½ ·ᴾ μ v)))
    pow∣½·2
    (mask-≈ ½ v H (½ ·ᴾ μ v) Q pow∣½·2 absQ (split-≈ ½ H (μ v) Q eq)))


------------------------------------------------------------------------
-- [Case]: ¼X + ½Q and ¼(1 - X) + ½Q′

-- A is the quarter q₁₀ of the phase (y_i, not y_j) and B the quarter
-- q₀₁ (y_j, not y_i).  X is read off A one digit below ½, then Q and
-- Q′ as ½-digits.

caseX : Poly n m → Poly n m
caseX A = readᴾ ½ ¼ A 0ᴾ

caseQ : Poly n m → Poly n m
caseQ A = readᴾ (pow M) ½ A (¼ ·ᴾ caseX A)

caseQ′ : Poly n m → Poly n m → Poly n m
caseQ′ A B = readᴾ (pow M) ½ B (¼ ·ᴾ (κ 1ℤ -ᴾ caseX A))

BoolValued-caseX : (A : Poly n m) → BoolValued (caseX A)
BoolValued-caseX A = BoolValued-readᴾ ½ ¼ A 0ᴾ

BoolValued-caseQ : (A : Poly n m) → BoolValued (caseQ A)
BoolValued-caseQ A = BoolValued-readᴾ (pow M) ½ A (¼ ·ᴾ caseX A)

BoolValued-caseQ′ : (A B : Poly n m) → BoolValued (caseQ′ A B)
BoolValued-caseQ′ A B =
  BoolValued-readᴾ (pow M) ½ B (¼ ·ᴾ (κ 1ℤ -ᴾ caseX A))

private
  swap-X : ∀ b h k x x₀ a →
           b - h * (k - x₀) ≡
           (b - h * (k - x)) - ((a - h * x₀) - (a - h * x))
  swap-X = solve 6 (λ b h k x x₀ a →
    b :- h :* (k :- x₀) :=
    (b :- h :* (k :- x)) :- ((a :- h :* x₀) :- (a :- h :* x))) refl

case-complete : (A B X Q Q′ : Poly n m) →
  A ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) →
  B ≈[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) →
  A ≈[ pow M ] ((¼ ·ᴾ caseX A) +ᴾ (½ ·ᴾ caseQ A)) ×
  B ≈[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ caseX A)) +ᴾ (½ ·ᴾ caseQ′ A B))
case-complete {n} {m} A B X Q Q′ e₁₀ e₀₁ =
  read-≈ ½ A (¼ ·ᴾ caseX A) (proj₁ r₁) pow∣½·2 (proj₂ r₁) ,
  read-≈ ½ B (¼ ·ᴾ (κ 1ℤ -ᴾ caseX A)) (proj₁ r₂) pow∣½·2 (proj₂ r₂)
  where
  -- Modulo ½ the ½-terms vanish.
  a₁ : A ≈[ ½ ] (¼ ·ᴾ X)
  a₁ = coarsen ½ A (¼ ·ᴾ X) Q ½∣pow ∣-refl e₁₀

  b₁ : B ≈[ ½ ] (¼ ·ᴾ (κ 1ℤ -ᴾ X))
  b₁ = coarsen ½ B (¼ ·ᴾ (κ 1ℤ -ᴾ X)) Q′ ½∣pow ∣-refl e₀₁

  -- The ¼-digits of A work for X ...
  a₂ : A ≈[ ½ ] (¼ ·ᴾ caseX A)
  a₂ = from-0 A (¼ ·ᴾ caseX A)
         (read-≈ ¼ A 0ᴾ X ½∣¼·2 (to-0 A (¼ ·ᴾ X) a₁))

  -- ... and then for B as well.
  b₂ : B ≈[ ½ ] (¼ ·ᴾ (κ 1ℤ -ᴾ caseX A))
  b₂ γ = subst (½ ∣_)
    (sym (swap-X (B γ) ¼ (κ 1ℤ γ) (X γ) (caseX A γ) (A γ)))
    (∣m∣n⇒∣m-n (b₁ γ) (∣m∣n⇒∣m-n (a₂ γ) (a₁ γ)))

  -- Back to 2^M, with some ½-terms, which the digits then replace.
  r₁ : Σ (Poly n m) (λ t → A ≈[ pow M ] ((¼ ·ᴾ caseX A) +ᴾ (½ ·ᴾ t)))
  r₁ = refine A (¼ ·ᴾ caseX A) a₂

  r₂ : Σ (Poly n m) (λ t →
         B ≈[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ caseX A)) +ᴾ (½ ·ᴾ t)))
  r₂ = refine B (¼ ·ᴾ (κ 1ℤ -ᴾ caseX A)) b₂
