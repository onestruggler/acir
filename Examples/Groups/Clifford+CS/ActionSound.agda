------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset action is sound: its rows spell what they claim
--
-- `act c y = (w , c′)` was defined so that, as matrices,
-- rep c · y = w · rep c′ (CosetAction).  Here that is derived in the
-- two-level presentation, row by row and then along a word (`run`):
-- the phases commute and i⁴ = ε, an exchange carries a phase on one
-- of its indices to the other, the sink of a K row is off the K.  So
-- a word that returns to the identity coset is spelled by the action's
-- output (`spell`): the translation of a two-level word of degree 0
-- into P′ is sound.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.ActionSound (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Data.Fin using (Fin ; zero ; toℕ) renaming (suc to fsuc ; _<_ to _<ᶠ_)
open import Data.List using ([] ; _∷_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Nat using (zero ; _+_ ; z≤n ; s≤s) renaming (suc to nsuc)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ʷ ; _ᵗ ; _^_)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (i ; X ; K ; i-gen ; X-gen ; K-gen)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (pw)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets
  using (Coset ; ⟨0⟩ ; ⟨1⟩ ; ⟨2⟩ ; ⟨3⟩ ; inc ; inc² ; pows)
open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big
  using (act ; rep ; 𝟎 ; Krow ; sink ; sink-off ; cos ; run-cos)
open import Examples.Groups.Clifford+CS.Auxiliary.SoundBase (suc N′)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc N′)
  using (swapF-a ; swapF-b)

private
  N : ℕ
  N = suc N′

  WT : Set
  WT = Word (TL.Gen N)

  WP : Set
  WP = Word (GenP N)

------------------------------------------------------------------------
-- Cosets as exponents

cnum : Coset → ℕ
cnum ⟨0⟩ = 0
cnum ⟨1⟩ = 1
cnum ⟨2⟩ = 2
cnum ⟨3⟩ = 3

-- A power written out is a power.
pows-^ : ∀ (w : WT) (c : Coset) → pows c w ≡ w ^ cnum c
pows-^ w ⟨0⟩ = Eq.refl
pows-^ w ⟨1⟩ = Eq.refl
pows-^ w ⟨2⟩ = Eq.refl
pows-^ w ⟨3⟩ = Eq.refl

-- The spelling of a power is the power of the spelling.
asG-pows : ∀ (w : WP) (c : Coset) → (asG ʷ) (pows c w) ≡ pows c ((asG ʷ) w)
asG-pows w ⟨0⟩ = Eq.refl
asG-pows w ⟨1⟩ = Eq.refl
asG-pows w ⟨2⟩ = Eq.refl
asG-pows w ⟨3⟩ = Eq.refl

-- The exponent one and two degrees up, as phases.
inc-^ : ∀ (c : Coset) (x : Fin N) → i x ^ cnum (inc c) ≈ i x ^ nsuc (cnum c)
inc-^ ⟨0⟩ x = refl
inc-^ ⟨1⟩ x = refl
inc-^ ⟨2⟩ x = refl
inc-^ ⟨3⟩ x = sym (i⁴ x)

inc²-^ : ∀ (c : Coset) (x : Fin N) → i x ^ cnum (inc² c) ≈ i x ^ (2 + cnum c)
inc²-^ ⟨0⟩ x = refl
inc²-^ ⟨1⟩ x = refl
inc²-^ ⟨2⟩ x = sym (i⁴ x)
inc²-^ ⟨3⟩ x = sym (i-mod4 x 1)

------------------------------------------------------------------------
-- Phase algebra

private
  -- A fourth power of a product of powers of one phase vanishes:
  -- (i x ^ a) ^ k • (i x) ^ k with a + 1 = 4.
  vanish : ∀ (x : Fin N) (k : ℕ) → (i x ^ 3) ^ k • i x ^ k ≈ ε
  vanish x k = begin
    (i x ^ 3) ^ k • i x ^ k    ≈⟨ sym (^-• (i x ^ 3) (i x) k (ipow-comm x x 3 1)) ⟩
    (i x ^ 3 • i x) ^ k        ≈⟨ ^-cong (i x ^ 3 • i x) (i x ^ 4) k (sym (^-+ (i x) 3 1)) ⟩
    (i x ^ 4) ^ k              ≈⟨ ^-cong (i x ^ 4) ε k (i⁴ x) ⟩
    ε ^ k                      ≈⟨ ε^k=ε k ⟩
    ε ∎

  -- The powers of two phases commute.
  pp-comm : ∀ (x y : Fin N) (a b : ℕ) → i x ^ a • i y ^ b ≈ i y ^ b • i x ^ a
  pp-comm = ipow-comm

  -- (i x • i y ^ 3) ^ k, collected.
  collect : ∀ (x y : Fin N) (k : ℕ) → (i x • i y ^ 3) ^ k ≈ i x ^ k • (i y ^ 3) ^ k
  collect x y k = ^-• (i x) (i y ^ 3) k (ipow-comm x y 1 3)

------------------------------------------------------------------------
-- The rows

-- A phase: rep c • i_[a] = (i_[a] i_[0]³) • rep (inc c).
row-i : ∀ (c : Coset) (a : Fin N) →
        rep c • i a ≈ (i a • i 𝟎 ^ 3) • rep (inc c)
row-i c a = begin
  pows c (i 𝟎) • i a
    ≈⟨ refl≡ (Eq.cong (_• i a) (pows-^ (i 𝟎) c)) ⟩
  i 𝟎 ^ k • i a
    ≈⟨ ipow-comm 𝟎 a k 1 ⟩
  i a • i 𝟎 ^ k
    ≈⟨ back (i a) (sym (i-mod4 𝟎 k)) ⟩
  i a • i 𝟎 ^ (4 + k)
    ≈⟨ back (i a) (^-+ (i 𝟎) 3 (nsuc k)) ⟩
  i a • (i 𝟎 ^ 3 • i 𝟎 ^ nsuc k)
    ≈⟨ back (i a) (back (i 𝟎 ^ 3) (sym (inc-^ c 𝟎))) ⟩
  i a • (i 𝟎 ^ 3 • i 𝟎 ^ cnum (inc c))
    ≈⟨ sym assoc ⟩
  (i a • i 𝟎 ^ 3) • i 𝟎 ^ cnum (inc c)
    ≈⟨ refl≡ (Eq.cong ((i a • i 𝟎 ^ 3) •_) (Eq.sym (pows-^ (i 𝟎) (inc c)))) ⟩
  (i a • i 𝟎 ^ 3) • pows (inc c) (i 𝟎) ∎
  where
  k = cnum c

-- An exchange on 0: rep c • X_[0,b] = ((−1)_[b] X_[0,b] (i_[b] i_[0]³)^c) • rep (inc² c).
row-X0 : ∀ (c : Coset) (b : Fin N) .(p : 𝟎 <ᶠ b) →
         rep c • X 𝟎 b p ≈ ((i b • (i b • X 𝟎 b p)) • pows c (i b • i 𝟎 ^ 3)) • rep (inc² c)
row-X0 c b p = begin
  pows c (i 𝟎) • Xb
    ≈⟨ refl≡ (Eq.cong (_• Xb) (pows-^ (i 𝟎) c)) ⟩
  i 𝟎 ^ k • Xb
    ≈⟨ cross-pow-at 𝟎 b p k (swapF-a 𝟎 b) ⟩
  Xb • i b ^ k
    ≈⟨ sym right-unit ⟩
  (Xb • i b ^ k) • ε
    ≈⟨ back _ (sym (i⁴ 𝟎)) ⟩
  (Xb • i b ^ k) • i 𝟎 ^ 4
    ≈⟨ back _ (^-+ (i 𝟎) 2 2) ⟩
  (Xb • i b ^ k) • (i 𝟎 ^ 2 • i 𝟎 ^ 2)
    ≈⟨ assoc ⟩
  Xb • (i b ^ k • (i 𝟎 ^ 2 • i 𝟎 ^ 2))
    ≈⟨ back Xb (sym assoc) ⟩
  Xb • ((i b ^ k • i 𝟎 ^ 2) • i 𝟎 ^ 2)
    ≈⟨ back Xb (front _ (ipow-comm b 𝟎 k 2)) ⟩
  Xb • ((i 𝟎 ^ 2 • i b ^ k) • i 𝟎 ^ 2)
    ≈⟨ back Xb assoc ⟩
  Xb • (i 𝟎 ^ 2 • (i b ^ k • i 𝟎 ^ 2))
    ≈⟨ sym assoc ⟩
  (Xb • i 𝟎 ^ 2) • (i b ^ k • i 𝟎 ^ 2)
    ≈⟨ front _ (sym (cross-pow-at 𝟎 b p 2 (swapF-b 𝟎 b))) ⟩
  (i b ^ 2 • Xb) • (i b ^ k • i 𝟎 ^ 2)
    ≈⟨ back _ (back (i b ^ k) (sym zeros)) ⟩
  (i b ^ 2 • Xb) • (i b ^ k • ((i 𝟎 ^ 3) ^ k • i 𝟎 ^ cnum (inc² c)))
    ≈⟨ back _ (sym assoc) ⟩
  (i b ^ 2 • Xb) • ((i b ^ k • (i 𝟎 ^ 3) ^ k) • i 𝟎 ^ cnum (inc² c))
    ≈⟨ back _ (front _ (sym (collect b 𝟎 k))) ⟩
  (i b ^ 2 • Xb) • ((i b • i 𝟎 ^ 3) ^ k • i 𝟎 ^ cnum (inc² c))
    ≈⟨ sym assoc ⟩
  ((i b ^ 2 • Xb) • (i b • i 𝟎 ^ 3) ^ k) • i 𝟎 ^ cnum (inc² c)
    ≈⟨ front _ (front _ assoc) ⟩
  ((i b • (i b • Xb)) • (i b • i 𝟎 ^ 3) ^ k) • i 𝟎 ^ cnum (inc² c)
    ≈⟨ refl≡ (Eq.cong₂ (λ u v → ((i b • (i b • Xb)) • u) • v)
                (Eq.sym (pows-^ (i b • i 𝟎 ^ 3) c)) (Eq.sym (pows-^ (i 𝟎) (inc² c)))) ⟩
  ((i b • (i b • Xb)) • pows c (i b • i 𝟎 ^ 3)) • pows (inc² c) (i 𝟎) ∎
  where
  k  = cnum c
  Xb = X 𝟎 b p

  -- (i_[0]³)^c • i_[0]^(c + 2) is i_[0]².
  zeros : (i 𝟎 ^ 3) ^ k • i 𝟎 ^ cnum (inc² c) ≈ i 𝟎 ^ 2
  zeros = begin
    (i 𝟎 ^ 3) ^ k • i 𝟎 ^ cnum (inc² c)    ≈⟨ back _ (inc²-^ c 𝟎) ⟩
    (i 𝟎 ^ 3) ^ k • i 𝟎 ^ (2 + k)          ≈⟨ back _ (^-+ (i 𝟎) 2 k) ⟩
    (i 𝟎 ^ 3) ^ k • (i 𝟎 ^ 2 • i 𝟎 ^ k)    ≈⟨ sym assoc ⟩
    ((i 𝟎 ^ 3) ^ k • i 𝟎 ^ 2) • i 𝟎 ^ k    ≈⟨ front _ (comm⇒pow-comm k 2 (ipow-comm 𝟎 𝟎 3 1)) ⟩
    (i 𝟎 ^ 2 • (i 𝟎 ^ 3) ^ k) • i 𝟎 ^ k    ≈⟨ assoc ⟩
    i 𝟎 ^ 2 • ((i 𝟎 ^ 3) ^ k • i 𝟎 ^ k)    ≈⟨ back _ (vanish 𝟎 k) ⟩
    i 𝟎 ^ 2 • ε                            ≈⟨ right-unit ⟩
    i 𝟎 ^ 2 ∎

-- An exchange off 0: rep c • X_[a,b] = ((−1)_[0] X_[a,b]) • rep (inc² c).
row-X : ∀ (c : Coset) (a b : Fin N) .(p : a <ᶠ b) → 𝟎 ≢ a → 𝟎 ≢ b →
        rep c • X a b p ≈ (i 𝟎 • (i 𝟎 • X a b p)) • rep (inc² c)
row-X c a b p za zb = begin
  pows c (i 𝟎) • Xab
    ≈⟨ refl≡ (Eq.cong (_• Xab) (pows-^ (i 𝟎) c)) ⟩
  i 𝟎 ^ k • Xab
    ≈⟨ sym (pass-pow (sym (axiom (TL.comm-iX p za zb))) k) ⟩
  Xab • i 𝟎 ^ k
    ≈⟨ back Xab (sym (i-mod4 𝟎 k)) ⟩
  Xab • i 𝟎 ^ (4 + k)
    ≈⟨ back Xab (^-+ (i 𝟎) 2 (2 + k)) ⟩
  Xab • (i 𝟎 ^ 2 • i 𝟎 ^ (2 + k))
    ≈⟨ back Xab (back _ (sym (inc²-^ c 𝟎))) ⟩
  Xab • (i 𝟎 ^ 2 • i 𝟎 ^ cnum (inc² c))
    ≈⟨ sym assoc ⟩
  (Xab • i 𝟎 ^ 2) • i 𝟎 ^ cnum (inc² c)
    ≈⟨ front _ (pass-pow (sym (axiom (TL.comm-iX p za zb))) 2) ⟩
  (i 𝟎 ^ 2 • Xab) • i 𝟎 ^ cnum (inc² c)
    ≈⟨ refl≡ (Eq.cong₂ (λ u v → u • v) Eq.refl (Eq.sym (pows-^ (i 𝟎) (inc² c)))) ⟩
  (i 𝟎 ^ 2 • Xab) • pows (inc² c) (i 𝟎)
    ≈⟨ front _ assoc ⟩
  (i 𝟎 • (i 𝟎 • Xab)) • pows (inc² c) (i 𝟎) ∎
  where
  k   = cnum c
  Xab = X a b p

-- A K: rep c • K_[d,e] = (i_[0] i_[t]⁻¹)^c · K i_[t]⁻¹ · (i_[t] i_[0]⁻¹)^(c+1) • rep (inc c).
private
  -- The algebra, with the exponents k = c and k′ = c + 1 mod 4.
  rowK : ∀ (d e t : Fin N) .(p : d <ᶠ e) → t ≢ d → t ≢ e → ∀ (k k′ : ℕ) →
         (∀ x → i x ^ k′ ≈ i x ^ nsuc k) →
         i 𝟎 ^ k • K d e p
         ≈ ((i 𝟎 • i t ^ 3) ^ k • ((K d e p • i t ^ 3) • (i t • i 𝟎 ^ 3) ^ k′)) • i 𝟎 ^ k′
  rowK d e t p td te k k′ H = sym (begin
    ((i 𝟎 • i t ^ 3) ^ k • ((Kde • C) • (i t • i 𝟎 ^ 3) ^ k′)) • F
      ≈⟨ front F (cong (collect 𝟎 t k) (back (Kde • C) (collect t 𝟎 k′))) ⟩
    ((A • B) • ((Kde • C) • (D • E))) • F
      ≈⟨ assoc ⟩
    (A • B) • (((Kde • C) • (D • E)) • F)
      ≈⟨ assoc ⟩
    A • (B • (((Kde • C) • (D • E)) • F))
      ≈⟨ back A (back B assoc) ⟩
    A • (B • ((Kde • C) • ((D • E) • F)))
      ≈⟨ back A (back B assoc) ⟩
    A • (B • (Kde • (C • ((D • E) • F))))
      ≈⟨ back A (sym assoc) ⟩
    A • ((B • Kde) • (C • ((D • E) • F)))
      ≈⟨ back A (front _ BK) ⟩
    A • ((Kde • B) • (C • ((D • E) • F)))
      ≈⟨ back A assoc ⟩
    A • (Kde • (B • (C • ((D • E) • F))))
      ≈⟨ back A (back Kde (back B (back C assoc))) ⟩
    A • (Kde • (B • (C • (D • (E • F)))))
      ≈⟨ back A (back Kde (back B (sym assoc))) ⟩
    A • (Kde • (B • ((C • D) • (E • F))))
      ≈⟨ back A (back Kde (sym assoc)) ⟩
    A • (Kde • ((B • (C • D)) • (E • F)))
      ≈⟨ back A (back Kde (cong ts (vanish 𝟎 k′))) ⟩
    A • (Kde • (ε • ε))
      ≈⟨ back A (back Kde left-unit) ⟩
    A • (Kde • ε)
      ≈⟨ back A right-unit ⟩
    A • Kde ∎)
    where
    Kde = K d e p
    A = i 𝟎 ^ k
    B = (i t ^ 3) ^ k
    C = i t ^ 3
    D = i t ^ k′
    E = (i 𝟎 ^ 3) ^ k′
    F = i 𝟎 ^ k′

    -- The K passes the phases on t.
    E₃ : Kde • i t ^ 3 ≈ i t ^ 3 • Kde
    E₃ = pass-pow {x = Kde} (sym (axiom (TL.comm-iK p td te))) 3

    BK : B • Kde ≈ Kde • B
    BK = sym (pass-pow {x = Kde} E₃ k)

    -- The phases on t: 3k + 3 + k′ ≡ 0.
    ts : B • (C • D) ≈ ε
    ts = begin
      (i t ^ 3) ^ k • (i t ^ 3 • i t ^ k′)
        ≈⟨ back _ (back _ (H t)) ⟩
      (i t ^ 3) ^ k • (i t ^ 3 • i t ^ nsuc k)
        ≈⟨ back _ (back _ (^-suc (i t) k)) ⟩
      (i t ^ 3) ^ k • (i t ^ 3 • (i t • i t ^ k))
        ≈⟨ back _ (sym assoc) ⟩
      (i t ^ 3) ^ k • ((i t ^ 3 • i t) • i t ^ k)
        ≈⟨ back _ (front _ (sym (^-+ (i t) 3 1))) ⟩
      (i t ^ 3) ^ k • (i t ^ 4 • i t ^ k)
        ≈⟨ back _ (front _ (i⁴ t)) ⟩
      (i t ^ 3) ^ k • (ε • i t ^ k)
        ≈⟨ back _ left-unit ⟩
      (i t ^ 3) ^ k • i t ^ k
        ≈⟨ vanish t k ⟩
      ε ∎

row-K : ∀ (c : Coset) (d e : Fin N) .(p : d <ᶠ e) →
        rep c • K d e p ≈ (asG ʷ) (Krow c d e p) • rep (inc c)
row-K c d e p = begin
  pows c (i 𝟎) • K d e p
    ≈⟨ refl≡ (Eq.cong (_• K d e p) (pows-^ (i 𝟎) c)) ⟩
  i 𝟎 ^ cnum c • K d e p
    ≈⟨ rowK d e t p td te (cnum c) (cnum (inc c)) (inc-^ c) ⟩
  ((i 𝟎 • i t ^ 3) ^ cnum c • ((K d e p • i t ^ 3) • (i t • i 𝟎 ^ 3) ^ cnum (inc c))) • i 𝟎 ^ cnum (inc c)
    ≈⟨ refl≡ (Eq.cong₂ _•_
         (Eq.cong₂ (λ u v → u • ((K d e p • i t ^ 3) • v))
           (Eq.sym (pows-^ (i 𝟎 • i t ^ 3) c)) (Eq.sym (pows-^ (i t • i 𝟎 ^ 3) (inc c))))
         (Eq.sym (pows-^ (i 𝟎) (inc c)))) ⟩
  (pows c (i 𝟎 • i t ^ 3) • ((K d e p • i t ^ 3) • pows (inc c) (i t • i 𝟎 ^ 3))) • pows (inc c) (i 𝟎)
    ≈⟨ refl≡ (Eq.cong (_• pows (inc c) (i 𝟎))
         (Eq.cong₂ _•_ (Eq.sym (asG-pows _ c))
           (Eq.cong ((K d e p • i t ^ 3) •_) (Eq.sym (asG-pows _ (inc c)))))) ⟩
  (asG ʷ) (Krow c d e p) • pows (inc c) (i 𝟎) ∎
  where
  t = sink d e

  td : t ≢ d
  td with sink-off d e
  ... | _ ∷ q ∷ _ = q

  te : t ≢ e
  te with sink-off d e
  ... | _ ∷ _ ∷ q ∷ _ = q

------------------------------------------------------------------------
-- Every generator, and every word

private
  -- The first index of an exchange on a successor is not 0, nor is
  -- its second.
  suc≢𝟎 : ∀ (a : Fin N′) → 𝟎 ≢ fsuc a
  suc≢𝟎 a ()

  <⇒≢𝟎 : ∀ {a : Fin N′} {b : Fin N} → .(fsuc a <ᶠ b) → 𝟎 ≢ b
  <⇒≢𝟎 {a} {zero} p = ⊥-elim (no p)
    where
    open import Data.Empty using (⊥-elim ; ⊥)
    no : .(fsuc a <ᶠ 𝟎) → ⊥
    no ()
  <⇒≢𝟎 {a} {fsuc b} p ()

row : ∀ (c : Coset) (y : TL.Gen N) →
      rep c • [ y ]ʷ ≈ (asG ʷ) (proj₁ (act c y)) • rep (proj₂ (act c y))
row c (i-gen a)             = row-i c a
row c (X-gen zero b p)      =
  Eq.subst (λ u → rep c • X 𝟎 b p ≈ ((i b • (i b • X 𝟎 b p)) • u) • rep (inc² c))
           (Eq.sym (asG-pows (pw b 𝟎) c)) (row-X0 c b p)
row c (X-gen (fsuc a) b p)  = row-X c (fsuc a) b p (suc≢𝟎 a) (<⇒≢𝟎 p)
row c (K-gen d e p)         = row-K c d e p

run : ∀ (c : Coset) (u : WT) →
      rep c • u ≈ (asG ʷ) (proj₁ ((act ᵗ) c u)) • rep (proj₂ ((act ᵗ) c u))
run c [ y ]ʷ  = row c y
run c ε       = trans right-unit (sym left-unit)
run c (u • v) = begin
  rep c • (u • v)
    ≈⟨ sym assoc ⟩
  (rep c • u) • v
    ≈⟨ front v (run c u) ⟩
  ((asG ʷ) wu • rep c′) • v
    ≈⟨ assoc ⟩
  (asG ʷ) wu • (rep c′ • v)
    ≈⟨ back _ (run c′ v) ⟩
  (asG ʷ) wu • ((asG ʷ) wv • rep c″)
    ≈⟨ sym assoc ⟩
  ((asG ʷ) wu • (asG ʷ) wv) • rep c″ ∎
  where
  c′ c″ : Coset
  c′ = proj₂ ((act ᵗ) c u)
  c″ = proj₂ ((act ᵗ) c′ v)

  wu wv : WP
  wu = proj₁ ((act ᵗ) c u)
  wv = proj₁ ((act ᵗ) c′ v)

-- A word that returns to the identity coset is spelled by the action's
-- output.
spell : ∀ (u : WT) → cos ⟨0⟩ u ≡ ⟨0⟩ → (asG ʷ) (proj₁ ((act ᵗ) ⟨0⟩ u)) ≈ u
spell u e = begin
  (asG ʷ) w
    ≈⟨ sym right-unit ⟩
  (asG ʷ) w • ε
    ≈⟨ refl≡ (Eq.cong (λ c → (asG ʷ) w • rep c) (Eq.sym (Eq.trans (run-cos ⟨0⟩ u) e))) ⟩
  (asG ʷ) w • rep (proj₂ ((act ᵗ) ⟨0⟩ u))
    ≈⟨ sym (run ⟨0⟩ u) ⟩
  ε • u
    ≈⟨ left-unit ⟩
  u ∎
  where
  w : WP
  w = proj₁ ((act ᵗ) ⟨0⟩ u)
