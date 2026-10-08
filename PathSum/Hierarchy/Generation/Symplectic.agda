------------------------------------------------------------------------
-- Presentations of groups
--
-- Pauli data from Pauli operators, and the symplectic form under
-- conjugation
--
-- Part of the generation of the n-qubit Clifford group (the plan is in
-- PathSum.Hierarchy.Generation.Scalar).  The synthesis of a circuit
-- for a Clifford operator U works on the Pauli data of the images
-- U X_j U† and U Z_j U†, and needs facts about those data that hold
-- because U is unitary.  They are proved here once, for every n:
--
--   * a Pauli operator determines its data: pauli p ≈ pauli q exactly
--     when p and q have the same bits and phases equal modulo 4
--     (pauli-inj, ≈ᴾ⇒≈; _≈ᴾ_ is that relation on data).  The entry of
--     pauli p from |0⟩ to |x⟩ is i^a and the one from |e_j⟩ to
--     |e_j ⊕ x⟩ is i^a (-1)^(z_j), and powers of ζ are distinct
--     modulo N (PathSum.Hierarchy.Levels's zpow-inj);
--   * so the sign of a Pauli is determined (sign-inj), and conjugation
--     by a unitary V preserves the symplectic form ω, which says
--     whether two Paulis commute (ω-pres): V P V† and V Q V† commute up
--     to the same sign as P and Q;
--   * ω with X_i reads the Z bit at i, ω with Z_i the X bit (ω-X,
--     ω-Z), so a unitary fixing X_i and Z_i sends every Pauli to one
--     with the same bits at wire i (conj-same), and the images of X_w
--     and Z_w anticommute (ω-XZ);
--   * the conjugate of a Hermitian operator is Hermitian (conj-herm),
--     X_w and Z_w are Hermitian, and a Hermitian Pauli whose bits have
--     z·x = 0 has the phase ±1 (herm-sign): i^a with a even.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Generation.Symplectic (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_; _%_; _/_)
open import Data.Integer.DivMod using (a≡a%n+[a/n]*n; n%d<d)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using
  (*-zeroʳ; *-identityʳ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; _<_; s≤s; z≤n)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using
  ([_]ᶻ; ≔-here; ≔-there; same; same-true; same-intro)
open import PathSum.Compose.Sum M₀ using (if-cong)
open import PathSum.Cyclotomic M₀ using (Amp; 0ᴬ; _≐_; zpow; N)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy.Generation.Scalar M₀ public
open import PathSum.Hierarchy.Levels M₀ using
  (zpow-inj; zpow-nonzero; quarters; ½≡¼·2; N≡¼·4)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ-neg; ≡ᴺ--; ≡ᴺ-N)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Equality of Pauli data

-- The same bits, and phases equal modulo 4.

infix 4 _≈ᴾ_

record _≈ᴾ_ {n : ℕ} (p q : PauliData n) : Set where
  constructor ≈ᴾ-intro
  field
    ph≈ : ¼ * ph p ≡ᴺ ¼ * ph q
    xs≈ : ∀ j → xs p j ≡ xs q j
    zs≈ : ∀ j → zs p j ≡ zs q j

open _≈ᴾ_ public

≈ᴾ-refl : {p : PauliData n} → p ≈ᴾ p
≈ᴾ-refl = ≈ᴾ-intro ≡ᴺ-refl (λ _ → refl) (λ _ → refl)

≈ᴾ-sym : {p q : PauliData n} → p ≈ᴾ q → q ≈ᴾ p
≈ᴾ-sym e = ≈ᴾ-intro (≡ᴺ-sym (ph≈ e)) (λ j → sym (xs≈ e j))
                    (λ j → sym (zs≈ e j))

≈ᴾ-trans : {p q r : PauliData n} → p ≈ᴾ q → q ≈ᴾ r → p ≈ᴾ r
≈ᴾ-trans e f = ≈ᴾ-intro (≡ᴺ-trans (ph≈ e) (ph≈ f))
                        (λ j → trans (xs≈ e j) (xs≈ f j))
                        (λ j → trans (zs≈ e j) (zs≈ f j))

≈ᴾ⇒≈ : {p q : PauliData n} → p ≈ᴾ q → pauli p ≈ pauli q
≈ᴾ⇒≈ {p = p} {q} e = pauli-≈ p q (ph≈ e) (xs≈ e) (zs≈ e)


------------------------------------------------------------------------
-- A Pauli operator determines its data

private
  -- Half a turn is not a whole one.

  ¬4∣ : (m : ℤ) {f : False ((+ 4) ∣? m)} → ¬ ((+ 4) ∣ m)
  ¬4∣ m {f} = toWitnessFalse f

  ½≢0 : ¬ (½ ≡ᴺ 0ℤ)
  ½≢0 = quarters ½ 0ℤ (+ 2) (trans (+-identityʳ ½) ½≡¼·2) (¬4∣ (+ 2))

  half-inj : (z z′ : Bool) → ½ * [ z ]ᶻ ≡ᴺ ½ * [ z′ ]ᶻ → z ≡ z′
  half-inj false false _ = refl
  half-inj true  true  _ = refl
  half-inj true  false h = ⊥-elim (½≢0
    (≡ᴺ-trans (≡ᴺ-≡ (sym (*-identityʳ ½))) (≡ᴺ-trans h (≡ᴺ-≡ (*-zeroʳ ½)))))
  half-inj false true  h = ⊥-elim (½≢0
    (≡ᴺ-trans (≡ᴺ-≡ (sym (*-identityʳ ½)))
              (≡ᴺ-trans (≡ᴺ-sym h) (≡ᴺ-≡ (*-zeroʳ ½)))))

  cancel-ᴺ : ∀ {a b c d} → a ≡ᴺ b → a + c ≡ᴺ b + d → c ≡ᴺ d
  cancel-ᴺ {a} {b} {c} {d} h₀ h₁ =
    ≡ᴺ-trans (≡ᴺ-≡ (left a c)) (≡ᴺ-trans (≡ᴺ-- h₁ h₀) (≡ᴺ-≡ (right b d)))
    where
    left : ∀ a c → c ≡ (a + c) - a
    left = solve 2 (λ a c → c := (a :+ c) :- a) refl
    right : ∀ b d → (b + d) - b ≡ d
    right = solve 2 (λ b d → (b :+ d) :- b := d) refl

  -- The entry of pauli p from v to v ⊕ x is ζ^(φ v).

  on-entry : (p : PauliData n) (v : Assign n) →
             mat (pauli p) v (v ⊕ᵛ xs p) ≐ zpow (φᴾ p v)
  on-entry p v = if-cong {p = same (v ⊕ᵛ xs p) (v ⊕ᵛ xs p)} {q = true}
    (same-intro (v ⊕ᵛ xs p) (v ⊕ᵛ xs p) (λ _ → refl)) ≐-refl

  -- The same entry of pauli q, when q flips the same bits.

  on-entry′ : (p q : PauliData n) (v : Assign n) →
              (∀ j → xs q j ≡ xs p j) →
              mat (pauli q) v (v ⊕ᵛ xs p) ≐ zpow (φᴾ q v)
  on-entry′ p q v xx = if-cong {p = same (v ⊕ᵛ xs q) (v ⊕ᵛ xs p)} {q = true}
    (same-intro (v ⊕ᵛ xs q) (v ⊕ᵛ xs p) (λ j → cong (v j xor_) (xx j)))
    ≐-refl

  -- At v = 0 the phase is i^a, at v = e_j it is i^a (-1)^(z_j).

  φ-0 : (p : PauliData n) → φᴾ p 0ᵛ ≡ ¼ * ph p + ½ * [ false ]ᶻ
  φ-0 p = cong (λ b → ¼ * ph p + ½ * [ b ]ᶻ) (dot-0ʳ (zs p) 0ᵛ (λ _ → refl))

  φ-e : (p : PauliData n) (j : Fin n) →
        φᴾ p (eᵛ j) ≡ ¼ * ph p + ½ * [ zs p j ]ᶻ
  φ-e p j = cong (λ b → ¼ * ph p + ½ * [ b ]ᶻ) (dot-e (zs p) j)

  ph0 : ∀ a → ¼ * a + ½ * [ false ]ᶻ ≡ ¼ * a
  ph0 a = trans (cong (λ t → ¼ * a + t) (*-zeroʳ ½)) (+-identityʳ (¼ * a))

-- The bits: the entry from |0⟩ to |x_p⟩ of pauli p is non-zero, so
-- pauli q flips the same bits.

pauli-inj-xs : (p q : PauliData n) → pauli p ≈ pauli q →
               ∀ j → xs q j ≡ xs p j
pauli-inj-xs p q e = from (same (0ᵛ ⊕ᵛ xs q) (xs p)) refl
  where
  from : ∀ b → same (0ᵛ ⊕ᵛ xs q) (xs p) ≡ b → ∀ j → xs q j ≡ xs p j
  from true  g = same-true (0ᵛ ⊕ᵛ xs q) (xs p) g
  from false g = ⊥-elim (zpow-nonzero (φᴾ p 0ᵛ)
    (≐-sym (on-entry p 0ᵛ) ∙ ≈-at e 0ᵛ (xs p)
     ∙ if-cong {p = same (0ᵛ ⊕ᵛ xs q) (xs p)} {q = false} g
               (≐-refl {a = zpow (φᴾ q 0ᵛ)})))

-- The phase, modulo 4: compare the entries from |0⟩.

pauli-inj-ph : (p q : PauliData n) → (∀ j → xs q j ≡ xs p j) →
               pauli p ≈ pauli q → ¼ * ph p ≡ᴺ ¼ * ph q
pauli-inj-ph p q xx e =
  ≡ᴺ-trans (≡ᴺ-≡ (sym (trans (φ-0 p) (ph0 (ph p)))))
    (≡ᴺ-trans (zpow-inj (≐-sym (on-entry p 0ᵛ) ∙ ≈-at e 0ᵛ (xs p)
                         ∙ on-entry′ p q 0ᵛ xx))
              (≡ᴺ-≡ (trans (φ-0 q) (ph0 (ph q)))))

-- The Z bits: compare the entries from |e_j⟩.

pauli-inj-zs : (p q : PauliData n) → (∀ j → xs q j ≡ xs p j) →
               pauli p ≈ pauli q → ∀ j → zs p j ≡ zs q j
pauli-inj-zs p q xx e j = half-inj (zs p j) (zs q j)
  (cancel-ᴺ {¼ * ph p} {¼ * ph q} (pauli-inj-ph p q xx e)
    (≡ᴺ-trans (≡ᴺ-≡ (sym (φ-e p j)))
      (≡ᴺ-trans (zpow-inj (≐-sym (on-entry p (eᵛ j))
                           ∙ ≈-at e (eᵛ j) (eᵛ j ⊕ᵛ xs p)
                           ∙ on-entry′ p q (eᵛ j) xx))
                (≡ᴺ-≡ (φ-e q j)))))

pauli-inj : {p q : PauliData n} → pauli p ≈ pauli q → p ≈ᴾ q
pauli-inj {p = p} {q} e =
  ≈ᴾ-intro (pauli-inj-ph p q xx e) (λ j → sym (xx j))
           (pauli-inj-zs p q xx e)
  where
  xx = pauli-inj-xs p q e

-- So equality of Pauli operators is equality of their data.

pauli⇔ : (p q : PauliData n) → (pauli p ≈ pauli q) ⇔ (p ≈ᴾ q)
pauli⇔ p q = mk⇔ pauli-inj ≈ᴾ⇒≈


------------------------------------------------------------------------
-- Signs, and the symplectic form

-- A sign is determined.

sign-inj : (b b′ : Bool) (c : PauliData n) →
           (½ * [ b ]ᶻ) ◃ pauli c ≈ (½ * [ b′ ]ᶻ) ◃ pauli c → b ≡ b′
sign-inj b b′ c e = half-inj b b′ (cancel-ᴺ {¼ * ph c} {¼ * ph c} ≡ᴺ-refl
  (≡ᴺ-trans (≡ᴺ-≡ (sym (split b)))
    (≡ᴺ-trans (ph≈ (pauli-inj
                      (≈-sym (sign-pauli b c) ⟨≈⟩ e ⟨≈⟩ sign-pauli b′ c)))
              (≡ᴺ-≡ (split b′)))))
  where
  split : ∀ s → ¼ * (ph c + (+ 2) * [ s ]ᶻ) ≡ ¼ * ph c + ½ * [ s ]ᶻ
  split s = trans (solve 3 (λ q a t → q :* (a :+ con (+ 2) :* t) :=
                                     q :* a :+ q :* (con (+ 2) :* t))
                          refl ¼ (ph c) [ s ]ᶻ)
                  (cong (λ t → ¼ * ph c + t) (¼·2 [ s ]ᶻ))

-- Conjugation by a unitary preserves the symplectic form: the
-- conjugates commute up to the sign the originals commute up to.

ω-pres : (V : Op n) → Unitary V → (a b a′ b′ : PauliData n) →
         V · pauli a · V † ≈ pauli a′ → V · pauli b · V † ≈ pauli b′ →
         ω a′ b′ ≡ ω a b
ω-pres V uV a b a′ b′ hA hB =
  sign-inj (ω a′ b′) (ω a b) (b′ ∙ᴾ a′)
    (◃-cong (½ * [ ω a′ b′ ]ᶻ) (≈-sym (pauli-· b′ a′))
     ⟨≈⟩ ≈-sym (pauli-comm a′ b′)
     ⟨≈⟩ ≈-sym (conj-split V (pauli a) (pauli b) uV ⟨≈⟩ ·-cong hA hB)
     ⟨≈⟩ conj-congᴾ V (pauli-comm a b)
     ⟨≈⟩ conj-◃ (½ * [ ω a b ]ᶻ) V (pauli b · pauli a)
     ⟨≈⟩ ◃-cong (½ * [ ω a b ]ᶻ)
           (conj-split V (pauli b) (pauli a) uV ⟨≈⟩ ·-cong hB hA
            ⟨≈⟩ pauli-· b′ a′))

-- ω with X_i reads the Z bit at i, ω with Z_i the X bit.

ω-X : (r : PauliData n) (i : Fin n) → ω r (X^ i) ≡ zs r i
ω-X r i = trans (cong₂ _xor_ (dot-e (zs r) i) (dot-0ˡ 0ᵛ (xs r) (λ _ → refl)))
                (xor-false (zs r i))

ω-Z : (r : PauliData n) (i : Fin n) → ω r (Z^ i) ≡ xs r i
ω-Z r i = cong₂ _xor_ (dot-0ʳ (zs r) 0ᵛ (λ _ → refl)) (e-dot i (xs r))

-- X_w and Z_w anticommute.

ω-XZ : (w : Fin n) → ω (X^ w) (Z^ w) ≡ true
ω-XZ w = trans (ω-Z (X^ w) w) (≔-here 0ᵛ w true)

-- The bits at a wire.

Same-at : Fin n → PauliData n → PauliData n → Set
Same-at i r s = (xs r i ≡ xs s i) × (zs r i ≡ zs s i)

Zero-at : Fin n → PauliData n → Set
Zero-at i r = (xs r i ≡ false) × (zs r i ≡ false)

-- A unitary fixing X_i and Z_i keeps the bits at wire i of every
-- Pauli it conjugates.

conj-same : (V : Op n) → Unitary V → (i : Fin n) →
            V · pauli (X^ i) · V † ≈ pauli (X^ i) →
            V · pauli (Z^ i) · V † ≈ pauli (Z^ i) →
            (s r : PauliData n) → V · pauli s · V † ≈ pauli r → Same-at i r s
conj-same V uV i fX fZ s r h =
  trans (sym (ω-Z r i))
    (trans (ω-pres V uV s (Z^ i) r (Z^ i) h fZ) (ω-Z s i)) ,
  trans (sym (ω-X r i))
    (trans (ω-pres V uV s (X^ i) r (X^ i) h fX) (ω-X s i))

-- Hence its images of X_w and Z_w are trivial at a wire i ≠ w.

conj-zero-X : (V : Op n) → Unitary V → (i w : Fin n) → i ≢ w →
              V · pauli (X^ i) · V † ≈ pauli (X^ i) →
              V · pauli (Z^ i) · V † ≈ pauli (Z^ i) →
              (r : PauliData n) → V · pauli (X^ w) · V † ≈ pauli r →
              Zero-at i r
conj-zero-X V uV i w i≢w fX fZ r h =
  let (sx , sz) = conj-same V uV i fX fZ (X^ w) r h
  in trans sx (≔-there 0ᵛ true i≢w) , sz

conj-zero-Z : (V : Op n) → Unitary V → (i w : Fin n) → i ≢ w →
              V · pauli (X^ i) · V † ≈ pauli (X^ i) →
              V · pauli (Z^ i) · V † ≈ pauli (Z^ i) →
              (r : PauliData n) → V · pauli (Z^ w) · V † ≈ pauli r →
              Zero-at i r
conj-zero-Z V uV i w i≢w fX fZ r h =
  let (sx , sz) = conj-same V uV i fX fZ (Z^ w) r h
  in sx , trans sz (≔-there 0ᵛ true i≢w)

-- The images of X_w and Z_w anticommute.

conj-anti : (V : Op n) → Unitary V → (w : Fin n) (p q : PauliData n) →
            V · pauli (X^ w) · V † ≈ pauli p →
            V · pauli (Z^ w) · V † ≈ pauli q → ω p q ≡ true
conj-anti V uV w p q hX hZ =
  trans (ω-pres V uV (X^ w) (Z^ w) p q hX hZ) (ω-XZ w)


------------------------------------------------------------------------
-- Hermitian Paulis

-- The conjugate of a Hermitian operator is Hermitian.

conj-herm : (V P R : Op n) → P † ≈ P → V · P · V † ≈ R → R † ≈ R
conj-herm V P R e h =
  †-cong (≈-sym h)
  ⟨≈⟩ †-· (V · P) (V †)
  ⟨≈⟩ ·-cong (†-involutive V) (†-· V P ⟨≈⟩ ·-congˡ (V †) e)
  ⟨≈⟩ ≈-sym (·-assoc V P (V †))
  ⟨≈⟩ h

-- X_w and Z_w are Hermitian.

X-herm : (w : Fin n) → pauli (X^ w) † ≈ pauli (X^ w)
X-herm w = pauli-† (X^ w) ⟨≈⟩ pauli-≈ (X^ w ⁻¹ᴾ) (X^ w)
  (≡ᴺ-≡ (cong (λ b → ¼ * (- 0ℤ + (+ 2) * [ b ]ᶻ))
               (dot-0ˡ 0ᵛ (eᵛ w) (λ _ → refl))))
  (λ _ → refl) (λ _ → refl)

Z-herm : (w : Fin n) → pauli (Z^ w) † ≈ pauli (Z^ w)
Z-herm w = pauli-† (Z^ w) ⟨≈⟩ pauli-≈ (Z^ w ⁻¹ᴾ) (Z^ w)
  (≡ᴺ-≡ (cong (λ b → ¼ * (- 0ℤ + (+ 2) * [ b ]ᶻ))
               (dot-0ʳ (eᵛ w) 0ᵛ (λ _ → refl))))
  (λ _ → refl) (λ _ → refl)

-- A Hermitian Pauli with z·x = 0 has the phase ±1.

private
  -- The phase read modulo 4.

  dist : ∀ f r q → f * (r + q * (+ 4)) ≡ f * r + q * (f * (+ 4))
  dist = solve 3 (λ f r q → f :* (r :+ q :* con (+ 4)) :=
                            f :* r :+ q :* (f :* con (+ 4))) refl

  mod4 : ∀ a → ¼ * a ≡ᴺ ¼ * (+ (a % (+ 4)))
  mod4 a = ≡ᴺ-trans (≡ᴺ-≡ step)
    (≡ᴺ-trans (≡ᴺ-+ (≡ᴺ-refl {¼ * (+ (a % (+ 4)))}) (≡ᴺ-N (a / (+ 4))))
              (≡ᴺ-≡ (+-identityʳ (¼ * (+ (a % (+ 4)))))))
    where
    step : ¼ * a ≡ ¼ * (+ (a % (+ 4))) + (a / (+ 4)) * (+ N)
    step = trans (cong (¼ *_) (a≡a%n+[a/n]*n a (+ 4)))
           (trans (dist ¼ (+ (a % (+ 4))) (a / (+ 4)))
                  (cong (λ t → ¼ * (+ (a % (+ 4))) + (a / (+ 4)) * t)
                        (sym N≡¼·4)))

  -- -(¼ k) ≡ ¼ k forces k ∈ {0, 2}.

  even-quarter : (k : ℕ) → k < 4 → - (¼ * (+ k)) ≡ᴺ ¼ * (+ k) →
                 Σ[ s ∈ Bool ] ¼ * (+ k) ≡ᴺ ½ * [ s ]ᶻ
  even-quarter 0 _ _ = false , ≡ᴺ-≡ (trans (*-zeroʳ ¼) (sym (*-zeroʳ ½)))
  even-quarter 1 _ h = ⊥-elim (quarters (- (¼ * (+ 1))) (¼ * (+ 1))
    (- (+ 2)) (solve 1 (λ q → :- (q :* con (+ 1)) :- q :* con (+ 1) :=
                              q :* con (- (+ 2))) refl ¼)
    (¬4∣ (- (+ 2))) h)
  even-quarter 2 _ _ = true , ≡ᴺ-≡ (trans (sym ½≡¼·2) (sym (*-identityʳ ½)))
  even-quarter 3 _ h = ⊥-elim (quarters (- (¼ * (+ 3))) (¼ * (+ 3))
    (- (+ 6)) (solve 1 (λ q → :- (q :* con (+ 3)) :- q :* con (+ 3) :=
                              q :* con (- (+ 6))) refl ¼)
    (¬4∣ (- (+ 6))) h)
  even-quarter (suc (suc (suc (suc k)))) (s≤s (s≤s (s≤s (s≤s ())))) _

herm-sign : (r : PauliData n) → pauli r † ≈ pauli r →
            dot (zs r) (xs r) ≡ false →
            Σ[ s ∈ Bool ] ¼ * ph r ≡ᴺ ½ * [ s ]ᶻ
herm-sign r h d =
  let (s , e) = even-quarter k (n%d<d (ph r) (+ 4)) neg-k
  in s , ≡ᴺ-trans (mod4 (ph r)) e
  where
  k = ph r % (+ 4)

  -- -(¼ a) ≡ ¼ a, from the phase of r† = r.
  neg : - (¼ * ph r) ≡ᴺ ¼ * ph r
  neg = ≡ᴺ-trans
    (≡ᴺ-≡ (trans (solve 2 (λ q a → :- (q :* a) :=
                                   q :* (:- a :+ con (+ 2) :* con 0ℤ))
                          refl ¼ (ph r))
                 (cong (λ b → ¼ * (- ph r + (+ 2) * [ b ]ᶻ)) (sym d))))
    (ph≈ (pauli-inj (≈-sym (pauli-† r) ⟨≈⟩ h)))

  neg-k : - (¼ * (+ k)) ≡ᴺ ¼ * (+ k)
  neg-k = ≡ᴺ-trans (≡ᴺ-neg (≡ᴺ-sym (mod4 (ph r))))
            (≡ᴺ-trans neg (mod4 (ph r)))
