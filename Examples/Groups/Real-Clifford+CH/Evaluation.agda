------------------------------------------------------------------------
-- Presentations of groups
--
-- A fast stored reading of circuits: the gates applied as row operations
--
-- ⟦ w ⟧M multiplies dense matrices: every gate is a full 2ᵏ × 2ᵏ trie
-- (tenM), and each product sums 2ᵏ terms for each of its entries.  A
-- gate of this set has at most two non-zero entries in a row, though, so
-- applying it on the left of a trie of rows is a row operation — a sum,
-- a difference or a scaling by ±√2 of whole rows — costing one
-- operation per entry.  `⟦_⟧R` reads a circuit that way, from the
-- right: run (w • v) R = run w (run v R), so run w R is ⟦ w ⟧ ⊙ R.
-- On a 40-gate three-wire equation that is roughly seven times less
-- work than ⟦_⟧M under the boolean check of Semantics.Decide.
--
-- `⟦⟧R-ix` is its correctness, as Interpretation.⟦⟧-ix is ⟦_⟧M's, and
-- `⟦⟧R≡⟦⟧M` says the two stored readings are the same trie.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Evaluation where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool using (true ; false)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁₊ ; ₂₊)

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation
  using (⟦_⟧ᵍ ; ⟦_⟧ₒ ; ⟦⟧ₒ-gen ; ⟦⟧ₒ-ε ; ⟦⟧ₒ-• ; ⟦_⟧M ; ⟦⟧-ix)

open import Examples.Groups.Real-Clifford+CH.Semantics.Decide using (eqM ; eqM-sound)

import Algebra.Properties.Ring as RingProps
open RingProps (CommutativeRing.ring +-*-commutativeRing) using (-‿distribˡ-*)

private
  variable
    k c : ℕ

------------------------------------------------------------------------
-- Tries of rows

-- A trie of 2ᵏ rows, each a trie of 2ᶜ entries.
Rows : ℕ → ℕ → Set
Rows k c = Tab k (Tab c 𝔽)

rix : Rows k c → Bits k → Bits c → 𝔽
rix R x y = get (get R x) y

mapT : ∀ k {A B : Set} → (A → B) → Tab k A → Tab k B
mapT ₀      f a        = f a
mapT (₁₊ k) f (a , a′) = mapT k f a , mapT k f a′

zipT : ∀ k {A B C : Set} → (A → B → C) → Tab k A → Tab k B → Tab k C
zipT ₀      f a        b        = f a b
zipT (₁₊ k) f (a , a′) (b , b′) = zipT k f a b , zipT k f a′ b′

get-map : ∀ k {A B : Set} (f : A → B) (t : Tab k A) (x : Bits k) →
          get (mapT k f t) x ≡ f (get t x)
get-map ₀      f t        []          = Eq.refl
get-map (₁₊ k) f (a , a′) (false ∷ x) = get-map k f a x
get-map (₁₊ k) f (a , a′) (true  ∷ x) = get-map k f a′ x

get-zip : ∀ k {A B C : Set} (f : A → B → C) (s : Tab k A) (t : Tab k B) (x : Bits k) →
          get (zipT k f s t) x ≡ f (get s x) (get t x)
get-zip ₀      f s        t        []          = Eq.refl
get-zip (₁₊ k) f (a , a′) (b , b′) (false ∷ x) = get-zip k f a b x
get-zip (₁₊ k) f (a , a′) (b , b′) (true  ∷ x) = get-zip k f a′ b′ x

------------------------------------------------------------------------
-- Row operations, every entry forced (Ring.strict)

private
  plus minus : 𝔽 → 𝔽 → 𝔽
  plus  a b = strict (a + b)
  minus a b = strict (a - b)

  times : 𝔽 → 𝔽 → 𝔽
  times s a = strict (s * a)

add sub : ∀ {k} c → Rows k c → Rows k c → Rows k c
add {k} c = zipT k (zipT c plus)
sub {k} c = zipT k (zipT c minus)

sc : ∀ {k} c → 𝔽 → Rows k c → Rows k c
sc {k} c s = mapT k (mapT c (times s))

rix-add : ∀ {k} c (l r : Rows k c) x y → rix (add {k} c l r) x y ≡ rix l x y + rix r x y
rix-add {k} c l r x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-zip k (zipT c plus) l r x))
    (Eq.trans (get-zip c plus (get l x) (get r x) y) (strict-id _))

rix-sub : ∀ {k} c (l r : Rows k c) x y → rix (sub {k} c l r) x y ≡ rix l x y - rix r x y
rix-sub {k} c l r x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-zip k (zipT c minus) l r x))
    (Eq.trans (get-zip c minus (get l x) (get r x) y) (strict-id _))

rix-sc : ∀ {k} c s (l : Rows k c) x y → rix (sc {k} c s l) x y ≡ s * rix l x y
rix-sc {k} c s l x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-map k (mapT c (times s)) l x))
    (Eq.trans (get-map c (times s) (get l x) y) (strict-id _))

------------------------------------------------------------------------
-- A generator on the left, as row operations

applyL : ∀ {k} c → Gen k → Rows k c → Rows k c
applyL c (gate₀ ())
applyL {₁₊ k} c H-gen  (l , r)                 = add {k} c l r , sub {k} c l r
applyL {₁₊ k} c Z-gen  (l , r)                 = sc {k} c √2 l , sc {k} c -√2 r
applyL {₂₊ k} c CZ-gen ((ll , lr) , (rl , rr)) =
  (sc {k} c √2 ll , sc {k} c √2 lr) , (sc {k} c √2 rl , sc {k} c -√2 rr)
applyL {₂₊ k} c CH-gen ((ll , lr) , (rl , rr)) =
  (sc {k} c √2 ll , add {k} c lr rr) , (sc {k} c √2 rl , sub {k} c lr rr)
applyL {₁₊ k} c (g ↥)  (l , r)                 = applyL {k} c g l , applyL {k} c g r

-- A word, from the right.
run : ∀ {k} c → Circuit k → Rows k c → Rows k c
run c [ g ]ʷ  R = applyL c g R
run c ε       R = R
run c (w • v) R = run c w (run c v R)

-- The reading.
⟦_⟧R : Circuit k → Mat k
⟦_⟧R {k} w = mat (run k w (entries (idM {k})))

------------------------------------------------------------------------
-- Correctness

-- An operator applied to a trie of rows.
_⊙ʳ_ : Op k → (Bits k → Bits c → 𝔽) → Bits k → Bits c → 𝔽
(G ⊙ʳ R) x y = Σb (λ z → G x z * R z y)

private
  -- A row of a gate: a constant times a delta.
  Σ-cδ : ∀ {n} (a : 𝔽) (x : Bits n) (f : Bits n → 𝔽) → Σb (λ z → (a * δb x z) * f z) ≡ a * f x
  Σ-cδ a x f =
    Eq.trans (Σ-cong {f = λ z → (a * δb x z) * f z} {g = λ z → a * (δb x z * f z)}
                     (λ z → *-assoc a (δb x z) (f z)))
      (Eq.trans (Σ-scaleˡ a (λ z → δb x z * f z)) (Eq.cong (a *_) (Σ-δˡ x f)))

  Σ-lin : ∀ {n} (a b : 𝔽) (x : Bits n) (f g : Bits n → 𝔽) →
          Σb (λ z → (a * δb x z) * f z) + Σb (λ z → (b * δb x z) * g z) ≡ a * f x + b * g x
  Σ-lin a b x f g = Eq.cong₂ _+_ (Σ-cδ a x f) (Σ-cδ b x g)

  Σ-lin₄ : ∀ {n} (a b c d : 𝔽) (x : Bits n) (f g h i : Bits n → 𝔽) →
           (Σb (λ z → (a * δb x z) * f z) + Σb (λ z → (b * δb x z) * g z)) +
           (Σb (λ z → (c * δb x z) * h z) + Σb (λ z → (d * δb x z) * i z)) ≡
           (a * f x + b * g x) + (c * h x + d * i x)
  Σ-lin₄ a b c d x f g h i = Eq.cong₂ _+_ (Σ-lin a b x f g) (Σ-lin c d x h i)

  -- The rows of the shifted gate: 1 or 0 times the gate's own row.
  Σ-1G : ∀ {n} (G : Op n) (x : Bits n) (f : Bits n → 𝔽) →
         Σb (λ z → (1# * G x z) * f z) ≡ Σb (λ z → G x z * f z)
  Σ-1G G x f = Σ-cong {f = λ z → (1# * G x z) * f z} {g = λ z → G x z * f z}
                      (λ z → Eq.cong (_* f z) (*-identityˡ (G x z)))

  Σ-0G : ∀ {n} (G : Op n) (x : Bits n) (f : Bits n → 𝔽) → Σb (λ z → (0# * G x z) * f z) ≡ 0#
  Σ-0G {n} G x f =
    Eq.trans (Σ-cong {f = λ z → (0# * G x z) * f z} {g = λ _ → 0#}
                     (λ z → Eq.trans (Eq.cong (_* f z) (*-zeroˡ (G x z))) (*-zeroˡ (f z))))
             (Σ-zero {n})

  -- The arithmetic of the rows.
  neg : ∀ a → -1# * a ≡ - a
  neg a = Eq.trans (Eq.sym (-‿distribˡ-* 1# a)) (-‿cong (*-identityˡ a))

  z : ∀ a → 0# * a ≡ 0#
  z = *-zeroˡ

  a+0 : ∀ a p → a + 0# * p ≡ a
  a+0 a p = Eq.trans (Eq.cong (a +_) (z p)) (+-identityʳ a)

  0+a : ∀ p a → 0# * p + a ≡ a
  0+a p a = Eq.trans (Eq.cong (_+ a) (z p)) (+-identityˡ a)

  zs : ∀ p q → 0# * p + 0# * q ≡ 0#
  zs p q = Eq.trans (0+a p (0# * q)) (z q)

  pos₁ : ∀ a p q r → (a + 0# * p) + (0# * q + 0# * r) ≡ a
  pos₁ a p q r = Eq.trans (Eq.cong₂ _+_ (a+0 a p) (zs q r)) (+-identityʳ a)

  pos₃ : ∀ a p q r → (0# * p + 0# * q) + (a + 0# * r) ≡ a
  pos₃ a p q r = Eq.trans (Eq.cong₂ _+_ (zs p q) (a+0 a r)) (+-identityˡ a)

  pos₄ : ∀ a p q r → (0# * p + 0# * q) + (0# * r + a) ≡ a
  pos₄ a p q r = Eq.trans (Eq.cong₂ _+_ (zs p q) (0+a r a)) (+-identityˡ a)

  pos₂₄ : ∀ p a q b → (0# * p + a) + (0# * q + b) ≡ a + b
  pos₂₄ p a q b = Eq.cong₂ _+_ (0+a p a) (0+a q b)

  one₂ : ∀ a b → 1# * a + 1# * b ≡ a + b
  one₂ a b = Eq.cong₂ _+_ (*-identityˡ a) (*-identityˡ b)

  onem : ∀ a b → 1# * a + -1# * b ≡ a - b
  onem a b = Eq.cong₂ _+_ (*-identityˡ a) (neg b)

-- A generator's row operation is its operator on the left.
applyL-ok : ∀ {k} c (g : Gen k) (R : Rows k c) x y →
            rix (applyL c g R) x y ≡ (⟦ g ⟧ᵍ ⊙ʳ rix R) x y
applyL-ok c (gate₀ ())
applyL-ok {₁₊ k} c H-gen (l , r) (false ∷ x) y =
  Eq.trans (rix-add c l r x y)
    (Eq.sym (Eq.trans (Σ-lin 1# 1# x (λ z → rix l z y) (λ z → rix r z y)) (one₂ _ _)))
applyL-ok {₁₊ k} c H-gen (l , r) (true ∷ x) y =
  Eq.trans (rix-sub c l r x y)
    (Eq.sym (Eq.trans (Σ-lin 1# -1# x (λ z → rix l z y) (λ z → rix r z y)) (onem _ _)))
applyL-ok {₁₊ k} c Z-gen (l , r) (false ∷ x) y =
  Eq.trans (rix-sc c √2 l x y)
    (Eq.sym (Eq.trans (Σ-lin √2 0# x (λ z → rix l z y) (λ z → rix r z y)) (a+0 _ _)))
applyL-ok {₁₊ k} c Z-gen (l , r) (true ∷ x) y =
  Eq.trans (rix-sc c -√2 r x y)
    (Eq.sym (Eq.trans (Σ-lin 0# -√2 x (λ z → rix l z y) (λ z → rix r z y)) (0+a _ _)))
applyL-ok {₂₊ k} c CZ-gen ((ll , lr) , (rl , rr)) (false ∷ false ∷ x) y =
  Eq.trans (rix-sc c √2 ll x y)
    (Eq.sym (Eq.trans (Σ-lin₄ √2 0# 0# 0# x (λ z → rix ll z y) (λ z → rix lr z y)
                                        (λ z → rix rl z y) (λ z → rix rr z y)) (pos₁ _ _ _ _)))
applyL-ok {₂₊ k} c CZ-gen ((ll , lr) , (rl , rr)) (false ∷ true ∷ x) y =
  Eq.trans (rix-sc c √2 lr x y)
    (Eq.sym (Eq.trans (Σ-lin₄ 0# √2 0# 0# x (λ z → rix ll z y) (λ z → rix lr z y)
                                        (λ z → rix rl z y) (λ z → rix rr z y))
                      (Eq.trans (Eq.cong₂ _+_ (0+a _ _) (zs _ _)) (+-identityʳ _))))
applyL-ok {₂₊ k} c CZ-gen ((ll , lr) , (rl , rr)) (true ∷ false ∷ x) y =
  Eq.trans (rix-sc c √2 rl x y)
    (Eq.sym (Eq.trans (Σ-lin₄ 0# 0# √2 0# x (λ z → rix ll z y) (λ z → rix lr z y)
                                        (λ z → rix rl z y) (λ z → rix rr z y)) (pos₃ _ _ _ _)))
applyL-ok {₂₊ k} c CZ-gen ((ll , lr) , (rl , rr)) (true ∷ true ∷ x) y =
  Eq.trans (rix-sc c -√2 rr x y)
    (Eq.sym (Eq.trans (Σ-lin₄ 0# 0# 0# -√2 x (λ z → rix ll z y) (λ z → rix lr z y)
                                         (λ z → rix rl z y) (λ z → rix rr z y)) (pos₄ _ _ _ _)))
applyL-ok {₂₊ k} c CH-gen ((ll , lr) , (rl , rr)) (false ∷ false ∷ x) y =
  Eq.trans (rix-sc c √2 ll x y)
    (Eq.sym (Eq.trans (Σ-lin₄ √2 0# 0# 0# x (λ z → rix ll z y) (λ z → rix lr z y)
                                        (λ z → rix rl z y) (λ z → rix rr z y)) (pos₁ _ _ _ _)))
applyL-ok {₂₊ k} c CH-gen ((ll , lr) , (rl , rr)) (false ∷ true ∷ x) y =
  Eq.trans (rix-add c lr rr x y)
    (Eq.sym (Eq.trans (Σ-lin₄ 0# 1# 0# 1# x (λ z → rix ll z y) (λ z → rix lr z y)
                                        (λ z → rix rl z y) (λ z → rix rr z y))
                      (Eq.trans (pos₂₄ _ _ _ _) (Eq.cong₂ _+_ (*-identityˡ _) (*-identityˡ _)))))
applyL-ok {₂₊ k} c CH-gen ((ll , lr) , (rl , rr)) (true ∷ false ∷ x) y =
  Eq.trans (rix-sc c √2 rl x y)
    (Eq.sym (Eq.trans (Σ-lin₄ 0# 0# √2 0# x (λ z → rix ll z y) (λ z → rix lr z y)
                                        (λ z → rix rl z y) (λ z → rix rr z y)) (pos₃ _ _ _ _)))
applyL-ok {₂₊ k} c CH-gen ((ll , lr) , (rl , rr)) (true ∷ true ∷ x) y =
  Eq.trans (rix-sub c lr rr x y)
    (Eq.sym (Eq.trans (Σ-lin₄ 0# 1# 0# -1# x (λ z → rix ll z y) (λ z → rix lr z y)
                                         (λ z → rix rl z y) (λ z → rix rr z y))
                      (Eq.trans (pos₂₄ _ _ _ _) (Eq.cong₂ _+_ (*-identityˡ _) (neg _)))))
applyL-ok {₁₊ k} c (g ↥) (l , r) (false ∷ x) y =
  Eq.trans (applyL-ok c g l x y)
    (Eq.sym (Eq.trans (Eq.cong₂ _+_ (Σ-1G ⟦ g ⟧ᵍ x (λ z → rix l z y)) (Σ-0G ⟦ g ⟧ᵍ x (λ z → rix r z y)))
                      (+-identityʳ _)))
applyL-ok {₁₊ k} c (g ↥) (l , r) (true ∷ x) y =
  Eq.trans (applyL-ok c g r x y)
    (Eq.sym (Eq.trans (Eq.cong₂ _+_ (Σ-0G ⟦ g ⟧ᵍ x (λ z → rix l z y)) (Σ-1G ⟦ g ⟧ᵍ x (λ z → rix r z y)))
                      (+-identityˡ _)))

private
  ⊙ʳ-cong : ∀ {G G′ : Op k} (R : Bits k → Bits c → 𝔽) → G ≐ G′ → ∀ x y → (G ⊙ʳ R) x y ≡ (G′ ⊙ʳ R) x y
  ⊙ʳ-cong {G = G} {G′} R e x y =
    Σ-cong {f = λ z → G x z * R z y} {g = λ z → G′ x z * R z y} (λ z → Eq.cong (_* R z y) (e x z))

  ⊙ʳ-ext : ∀ (G : Op k) {R S : Bits k → Bits c → 𝔽} → (∀ x y → R x y ≡ S x y) →
           ∀ x y → (G ⊙ʳ R) x y ≡ (G ⊙ʳ S) x y
  ⊙ʳ-ext G {R} {S} e x y =
    Σ-cong {f = λ z → G x z * R z y} {g = λ z → G x z * S z y} (λ z → Eq.cong (G x z *_) (e z y))

  ⊙ʳ-assoc : (M N : Op k) (R : Bits k → Bits c → 𝔽) → ∀ x y →
             (M ⊙ʳ (N ⊙ʳ R)) x y ≡ ((M ⊙ N) ⊙ʳ R) x y
  ⊙ʳ-assoc M N R x y = begin
    Σb (λ z → M x z * Σb (λ w → N z w * R w y))
      ≡⟨ Σ-cong {f = λ z → M x z * Σb (λ w → N z w * R w y)}
                {g = λ z → Σb (λ w → (M x z * N z w) * R w y)}
                (λ z → Eq.trans (Eq.sym (Σ-scaleˡ (M x z) (λ w → N z w * R w y)))
                         (Σ-cong {f = λ w → M x z * (N z w * R w y)}
                                 {g = λ w → (M x z * N z w) * R w y}
                                 (λ w → Eq.sym (*-assoc (M x z) (N z w) (R w y))))) ⟩
    Σb (λ z → Σb (λ w → (M x z * N z w) * R w y))
      ≡⟨ Σ-swap (λ z w → (M x z * N z w) * R w y) ⟩
    Σb (λ w → Σb (λ z → (M x z * N z w) * R w y))
      ≡⟨ Σ-cong {f = λ w → Σb (λ z → (M x z * N z w) * R w y)}
                {g = λ w → Σb (λ z → M x z * N z w) * R w y}
                (λ w → Σ-scaleʳ (R w y) (λ z → M x z * N z w)) ⟩
    Σb (λ w → Σb (λ z → M x z * N z w) * R w y) ∎
    where open Eq.≡-Reasoning

  ⊙ʳ-id : (R : Bits k → Bits c → 𝔽) → ∀ x y → (Idₒ ⊙ʳ R) x y ≡ R x y
  ⊙ʳ-id R x y = Σ-δˡ x (λ z → R z y)

-- A word's row operations are its operator on the left.
run-ok : ∀ {k} c (w : Circuit k) (R : Rows k c) x y → rix (run c w R) x y ≡ (⟦ w ⟧ₒ ⊙ʳ rix R) x y
run-ok c [ g ]ʷ  R x y = Eq.trans (applyL-ok c g R x y) (Eq.sym (⊙ʳ-cong (rix R) (⟦⟧ₒ-gen g) x y))
run-ok c ε       R x y = Eq.sym (Eq.trans (⊙ʳ-cong (rix R) ⟦⟧ₒ-ε x y) (⊙ʳ-id (rix R) x y))
run-ok c (w • v) R x y =
  Eq.trans (run-ok c w (run c v R) x y)
    (Eq.trans (⊙ʳ-ext ⟦ w ⟧ₒ (run-ok c v R) x y)
      (Eq.trans (⊙ʳ-assoc ⟦ w ⟧ₒ ⟦ v ⟧ₒ (rix R) x y)
                (Eq.sym (⊙ʳ-cong (rix R) (⟦⟧ₒ-• w v) x y))))

-- At its own width, a circuit's operator is its row-operation reading.
⟦⟧R-ix : (w : Circuit k) → ⟦ w ⟧ₒ ≐ ix ⟦ w ⟧R
⟦⟧R-ix {k} w x y = Eq.sym
  (Eq.trans (run-ok k w (entries (idM {k})) x y)
    (Eq.trans (⊙ʳ-ext ⟦ w ⟧ₒ (ix-id {k}) x y)
              (Σ-δʳ y (λ z → ⟦ w ⟧ₒ x z))))

-- The two stored readings are the same trie.
⟦⟧R≡⟦⟧M : (w : Circuit k) → ⟦ w ⟧R ≡ ⟦ w ⟧M
⟦⟧R≡⟦⟧M w = mat-ext (≐-trans (≐-sym (⟦⟧R-ix w)) (⟦⟧-ix w))

-- A stored-matrix identity, decided by one boolean on the row-operation
-- reading (Semantics.Decide): `by-rows w Eq.refl : ⟦ w ⟧M ≡ L` evaluates
-- w once, where `Eq.refl` at that type evaluates the dense product once
-- per entry of L.
by-rows : (w : Circuit k) {L : Mat k} → eqM ⟦ w ⟧R L ≡ true → ⟦ w ⟧M ≡ L
by-rows w e = Eq.trans (Eq.sym (⟦⟧R≡⟦⟧M w)) (eqM-sound _ _ e)
