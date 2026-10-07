------------------------------------------------------------------------
-- Presentations of groups
--
-- One qubit: Pauli codes
--
-- A single-qubit Pauli i^a X^x Z^z as a Code (a, x, z), its operator
-- pauli ⟦ c ⟧ᶜ, products, phases and adjoints read off the codes, the
-- phase normalised modulo 4 (nc), and the codes read back from the
-- operators: letters and code-inj.  Part of PathSum.Hierarchy.OneQubit.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.OneQubit.Code (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _∨_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; -[1+_]; _+_; _-_; _*_; _%_; _/_)
open import Data.Integer.DivMod using (a≡a%n+[a/n]*n; n%d<d)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using
  (_≟_; *-zeroʳ; *-identityʳ; +-identityˡ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero; _<_; z≤n; s≤s)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; lookup)
  renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Nullary.Decidable using
  (⌊_⌋; yes; no; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using
  ([_]ᶻ; _=ᵇ_; =ᵇ-refl; =ᵇ-true; same; same-≗; ≔-here)
open import PathSum.Compose.Matrix M₀ using (if-⊛; ⊛-if)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong; zpow-≡; scale-exp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; -ᴬ_; _≐_; Σᴮ-cong; zpow; rot; rot-exp; rot-0; rot-anti;
   scale-injective; N)
  renaming (H to Hᶻ)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy M₀
open import PathSum.Hierarchy.Gates M₀
open import PathSum.Hierarchy.Levels M₀
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ--; ≡ᴺ-N)
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong)
open import PathSum.Ring.Laws M₀ using (⊛-comm)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Booleans

∧-l : (a b : Bool) → a ∧ b ≡ true → a ≡ true
∧-l true  _ _ = refl
∧-l false _ ()

∧-r : (a b : Bool) → a ∧ b ≡ true → b ≡ true
∧-r true  _ h = h
∧-r false _ ()

∧-intro : (a b : Bool) → a ≡ true → b ≡ true → a ∧ b ≡ true
∧-intro true true _ _ = refl

∨-not : (a b : Bool) → a ≡ true → not a ∨ b ≡ true → b ≡ true
∨-not _ _ refl h = h

=ᶻ-refl : (a : ℤ) → ⌊ a ≟ a ⌋ ≡ true
=ᶻ-refl a with a ≟ a
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

=ᶻ-sound : (a b : ℤ) → ⌊ a ≟ b ⌋ ≡ true → a ≡ b
=ᶻ-sound a b h with a ≟ b
=ᶻ-sound a b h  | yes p = p
=ᶻ-sound a b () | no _

=ᶠ-sound : {m : ℕ} (i j : Fin m) → ⌊ i Fin.≟ j ⌋ ≡ true → i ≡ j
=ᶠ-sound i j h with i Fin.≟ j
=ᶠ-sound i j h  | yes p = p
=ᶠ-sound i j () | no _

neg-fixed : (a : ℤ) → a ≡ - a → a ≡ 0ℤ
neg-fixed (+ zero)  _ = refl
neg-fixed (+ suc n) ()
neg-fixed -[1+ n ]  ()


------------------------------------------------------------------------
-- One qubit

w₀ : Fin 1
w₀ = zero

-- The constant assignments, and the two basis states.

const : Bool → Assign 1
const b _ = b

0₁ 1₁ : Assign 1
0₁ = const false
1₁ = const true

-- An assignment to one wire is constant.

on₁ : (v : Assign 1) → ∀ j → v j ≡ const (v w₀) j
on₁ v zero = refl
on₁ v (suc ())


------------------------------------------------------------------------
-- Pauli codes

-- The code of i^a X^x Z^z.

record Code : Set where
  constructor code
  field
    cph : ℤ
    cx cz : Bool

open Code public

⟦_⟧ᶜ : Code → PauliData 1
⟦ c ⟧ᶜ = pd (cph c) (const (cx c)) (const (cz c))

c1 cX cZ : Code
c1 = code 0ℤ false false
cX = code 0ℤ true false
cZ = code 0ℤ false true

-- Equal codes give equal Paulis.  Used, with refl, to move between
-- two spellings of one code without comparing operators.

code≡ : (c d : Code) → c ≡ d → pauli ⟦ c ⟧ᶜ ≈ pauli ⟦ d ⟧ᶜ
code≡ c .c refl = ≈-refl

-- Every Pauli on one qubit has a code.

toC : PauliData 1 → Code
toC p = code (ph p) (xs p w₀) (zs p w₀)

toC-≈ : (p : PauliData 1) → pauli p ≈ pauli ⟦ toC p ⟧ᶜ
toC-≈ p = pauli-≈ p ⟦ toC p ⟧ᶜ ≡ᴺ-refl (on₁ (xs p)) (on₁ (zs p))

-- The generators.

X≈ : pauli (X^ w₀) ≈ pauli ⟦ cX ⟧ᶜ
X≈ = pauli-≈ (X^ w₀) ⟦ cX ⟧ᶜ ≡ᴺ-refl xx (λ _ → refl)
  where
  xx : ∀ j → eᵛ w₀ j ≡ true
  xx zero = ≔-here 0ᵛ w₀ true
  xx (suc ())

Z≈ : pauli (Z^ w₀) ≈ pauli ⟦ cZ ⟧ᶜ
Z≈ = pauli-≈ (Z^ w₀) ⟦ cZ ⟧ᶜ ≡ᴺ-refl (λ _ → refl) zz
  where
  zz : ∀ j → eᵛ w₀ j ≡ true
  zz zero = ≔-here 0ᵛ w₀ true
  zz (suc ())

c1≈I : pauli ⟦ c1 ⟧ᶜ ≈ I
c1≈I = pauli-≈ ⟦ c1 ⟧ᶜ 1ᴾ ≡ᴺ-refl (λ _ → refl) (λ _ → refl) ⟨≈⟩ pauli-I

-- Products, phases and adjoints of codes.

infixl 7 _·ᶜ_

_·ᶜ_ : Code → Code → Code
c ·ᶜ d = code (cph c + cph d + (+ 2) * [ cz c ∧ cx d ]ᶻ)
              (cx c xor cx d) (cz c xor cz d)

shiftᶜ : ℤ → Code → Code
shiftᶜ t c = code (cph c + t) (cx c) (cz c)

invᶜ : Code → Code
invᶜ c = code (- cph c + (+ 2) * [ cz c ∧ cx c ]ᶻ) (cx c) (cz c)

dot₁ : (a b : Bool) → dot (const a) (const b) ≡ a ∧ b
dot₁ a b = xor-false (a ∧ b)

·ᶜ-ok : (c d : Code) → pauli ⟦ c ⟧ᶜ · pauli ⟦ d ⟧ᶜ ≈ pauli ⟦ c ·ᶜ d ⟧ᶜ
·ᶜ-ok c d =
  pauli-· ⟦ c ⟧ᶜ ⟦ d ⟧ᶜ
  ⟨≈⟩ pauli-≈ (⟦ c ⟧ᶜ ∙ᴾ ⟦ d ⟧ᶜ) ⟦ c ·ᶜ d ⟧ᶜ
        (≡ᴺ-≡ (cong (λ b → ¼ * (cph c + cph d + (+ 2) * [ b ]ᶻ))
                    (dot₁ (cz c) (cx d))))
        (λ _ → refl) (λ _ → refl)

◃-code : (t : ℤ) (c : Code) → (¼ * t) ◃ pauli ⟦ c ⟧ᶜ ≈ pauli ⟦ shiftᶜ t c ⟧ᶜ
◃-code t c =
  ◃-pauli t ⟦ c ⟧ᶜ
  ⟨≈⟩ pauli-≈ (pd (ph ⟦ c ⟧ᶜ + t) (xs ⟦ c ⟧ᶜ) (zs ⟦ c ⟧ᶜ)) ⟦ shiftᶜ t c ⟧ᶜ
        ≡ᴺ-refl (λ _ → refl) (λ _ → refl)

†-code : (c : Code) → pauli ⟦ c ⟧ᶜ † ≈ pauli ⟦ invᶜ c ⟧ᶜ
†-code c =
  pauli-† ⟦ c ⟧ᶜ
  ⟨≈⟩ pauli-≈ (⟦ c ⟧ᶜ ⁻¹ᴾ) ⟦ invᶜ c ⟧ᶜ
        (≡ᴺ-≡ (cong (λ b → ¼ * (- cph c + (+ 2) * [ b ]ᶻ))
                    (dot₁ (cz c) (cx c))))
        (λ _ → refl) (λ _ → refl)

-- i^a X^x Z^z is i^a times X^x times Z^z.

decomp : (c : Code) →
         pauli ⟦ c ⟧ᶜ ≈
         (¼ * cph c) ◃ (pauli ⟦ code 0ℤ (cx c) false ⟧ᶜ ·
                        pauli ⟦ code 0ℤ false (cz c) ⟧ᶜ)
decomp c = ≈-sym (
  ◃-cong (¼ * cph c) (·ᶜ-ok (code 0ℤ (cx c) false) (code 0ℤ false (cz c)))
  ⟨≈⟩ ◃-code (cph c) (code 0ℤ (cx c) false ·ᶜ code 0ℤ false (cz c))
  ⟨≈⟩ pauli-≈ ⟦ shiftᶜ (cph c) (code 0ℤ (cx c) false ·ᶜ code 0ℤ false (cz c)) ⟧ᶜ
              ⟦ c ⟧ᶜ
        (≡ᴺ-≡ (cong (¼ *_) (+-identityˡ (cph c))))
        (λ _ → xor-false (cx c)) (λ _ → refl))


------------------------------------------------------------------------
-- Normalised codes

-- The phase read modulo 4.

nc : Code → Code
nc c = code (+ (cph c % (+ 4))) (cx c) (cz c)

nc-≈ : (c : Code) → pauli ⟦ c ⟧ᶜ ≈ pauli ⟦ nc c ⟧ᶜ
nc-≈ c = pauli-≈ ⟦ c ⟧ᶜ ⟦ nc c ⟧ᶜ (nc-phase (cph c)) (λ _ → refl) (λ _ → refl)
  where
  dist : ∀ f r q → f * (r + q * (+ 4)) ≡ f * r + q * (f * (+ 4))
  dist = solve 3 (λ f r q → f :* (r :+ q :* con (+ 4)) :=
                            f :* r :+ q :* (f :* con (+ 4))) refl

  nc-phase : ∀ a → ¼ * a ≡ᴺ ¼ * (+ (a % (+ 4)))
  nc-phase a = ≡ᴺ-trans (≡ᴺ-≡ step)
    (≡ᴺ-trans (≡ᴺ-+ (≡ᴺ-refl {¼ * (+ (a % (+ 4)))}) (≡ᴺ-N (a / (+ 4))))
              (≡ᴺ-≡ (+-identityʳ (¼ * (+ (a % (+ 4)))))))
    where
    step : ¼ * a ≡ ¼ * (+ (a % (+ 4))) + (a / (+ 4)) * (+ N)
    step = trans (cong (¼ *_) (a≡a%n+[a/n]*n a (+ 4)))
           (trans (dist ¼ (+ (a % (+ 4))) (a / (+ 4)))
                  (cong (λ t → ¼ * (+ (a % (+ 4))) + (a / (+ 4)) * t)
                        (sym N≡¼·4)))

-- Reading a code back from its Pauli's entries.

private
  ph0 : ∀ a → ¼ * a + ½ * 0ℤ ≡ ¼ * a
  ph0 a = trans (cong (λ t → ¼ * a + t) (*-zeroʳ ½)) (+-identityʳ (¼ * a))

  e₀ : (a : ℤ) (x z : Bool) →
       mat (pauli ⟦ code a x z ⟧ᶜ) 0₁ (const x) ≐ zpow (¼ * a)
  e₀ a false false = zpow-≡ (ph0 a)
  e₀ a false true  = zpow-≡ (ph0 a)
  e₀ a true  false = zpow-≡ (ph0 a)
  e₀ a true  true  = zpow-≡ (ph0 a)

  e₁ : (a : ℤ) (x z : Bool) →
       mat (pauli ⟦ code a x z ⟧ᶜ) 1₁ (const (not x)) ≐
       zpow (¼ * a + ½ * [ z ]ᶻ)
  e₁ a false false _ = refl
  e₁ a false true  _ = refl
  e₁ a true  false _ = refl
  e₁ a true  true  _ = refl

  eoff : (a : ℤ) (x z : Bool) →
         mat (pauli ⟦ code a x z ⟧ᶜ) 0₁ (const (not x)) ≐ 0ᴬ
  eoff a false z _ = refl
  eoff a true  z _ = refl

  x-inj : (a b : ℤ) (x z x′ z′ : Bool) →
          pauli ⟦ code a x z ⟧ᶜ ≈ pauli ⟦ code b x′ z′ ⟧ᶜ → x ≡ x′
  x-inj a b false z false z′ e = refl
  x-inj a b true  z true  z′ e = refl
  x-inj a b false z true  z′ e = ⊥-elim (zpow-nonzero (¼ * a)
    (≐-sym (e₀ a false z) ∙ ≈-at e 0₁ (const false) ∙ eoff b true z′))
  x-inj a b true  z false z′ e = ⊥-elim (zpow-nonzero (¼ * a)
    (≐-sym (e₀ a true z) ∙ ≈-at e 0₁ (const true) ∙ eoff b false z′))

  ½≢0 : ¬ (½ ≡ᴺ 0ℤ)
  ½≢0 = quarters ½ 0ℤ (+ 2) (trans (+-identityʳ ½) ½≡¼·2)
                 (4∤ 2 (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))))

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

  same-x : (a b : ℤ) (x z z′ : Bool) →
           pauli ⟦ code a x z ⟧ᶜ ≈ pauli ⟦ code b x z′ ⟧ᶜ →
           (¼ * a ≡ᴺ ¼ * b) × (z ≡ z′)
  same-x a b x z z′ e =
    ph≡ , half-inj z z′ (cancel-ᴺ {¼ * a} {¼ * b} {½ * [ z ]ᶻ} {½ * [ z′ ]ᶻ}
                                  ph≡ ph₁)
    where
    ph≡ : ¼ * a ≡ᴺ ¼ * b
    ph≡ = zpow-inj (≐-sym (e₀ a x z) ∙ ≈-at e 0₁ (const x) ∙ e₀ b x z′)
    ph₁ : ¼ * a + ½ * [ z ]ᶻ ≡ᴺ ¼ * b + ½ * [ z′ ]ᶻ
    ph₁ = zpow-inj (≐-sym (e₁ a x z) ∙ ≈-at e 1₁ (const (not x)) ∙ e₁ b x z′)

  letters-z : (a b : ℤ) (x z x′ z′ : Bool) → x ≡ x′ →
              pauli ⟦ code a x z ⟧ᶜ ≈ pauli ⟦ code b x′ z′ ⟧ᶜ → z ≡ z′
  letters-z a b x z .x z′ refl e = proj₂ (same-x a b x z z′ e)

-- Equal Paulis have the same letters.

letters : (c d : Code) → pauli ⟦ c ⟧ᶜ ≈ pauli ⟦ d ⟧ᶜ →
          (cx c ≡ cx d) × (cz c ≡ cz d)
letters (code a x z) (code b x′ z′) e =
  x-inj a b x z x′ z′ e , letters-z a b x z x′ z′ (x-inj a b x z x′ z′ e) e

-- Phases 0, 1, 2, 3 of i are distinct.

private
  ¬4∣ : (m : ℤ) {f : False ((+ 4) ∣? m)} → ¬ ((+ 4) ∣ m)
  ¬4∣ m {f} = toWitnessFalse f

  q-diff : ∀ a b → ¼ * a - ¼ * b ≡ ¼ * (a - b)
  q-diff a b = solve 3 (λ q a b → q :* a :- q :* b := q :* (a :- b)) refl ¼ a b

  off : (k l : ℕ) → ¬ ((+ 4) ∣ ((+ k) - (+ l))) →
        ¬ (¼ * (+ k) ≡ᴺ ¼ * (+ l))
  off k l ¬4 = quarters (¼ * (+ k)) (¼ * (+ l)) ((+ k) - (+ l))
                        (q-diff (+ k) (+ l)) ¬4

  phase-inj : (k l : ℕ) → k < 4 → l < 4 → ¼ * (+ k) ≡ᴺ ¼ * (+ l) → k ≡ l
  phase-inj 0 0 _ _ _ = refl
  phase-inj 0 1 _ _ h = ⊥-elim (off 0 1 (¬4∣ ((+ 0) - (+ 1))) h)
  phase-inj 0 2 _ _ h = ⊥-elim (off 0 2 (¬4∣ ((+ 0) - (+ 2))) h)
  phase-inj 0 3 _ _ h = ⊥-elim (off 0 3 (¬4∣ ((+ 0) - (+ 3))) h)
  phase-inj 1 0 _ _ h = ⊥-elim (off 1 0 (¬4∣ ((+ 1) - (+ 0))) h)
  phase-inj 1 1 _ _ _ = refl
  phase-inj 1 2 _ _ h = ⊥-elim (off 1 2 (¬4∣ ((+ 1) - (+ 2))) h)
  phase-inj 1 3 _ _ h = ⊥-elim (off 1 3 (¬4∣ ((+ 1) - (+ 3))) h)
  phase-inj 2 0 _ _ h = ⊥-elim (off 2 0 (¬4∣ ((+ 2) - (+ 0))) h)
  phase-inj 2 1 _ _ h = ⊥-elim (off 2 1 (¬4∣ ((+ 2) - (+ 1))) h)
  phase-inj 2 2 _ _ _ = refl
  phase-inj 2 3 _ _ h = ⊥-elim (off 2 3 (¬4∣ ((+ 2) - (+ 3))) h)
  phase-inj 3 0 _ _ h = ⊥-elim (off 3 0 (¬4∣ ((+ 3) - (+ 0))) h)
  phase-inj 3 1 _ _ h = ⊥-elim (off 3 1 (¬4∣ ((+ 3) - (+ 1))) h)
  phase-inj 3 2 _ _ h = ⊥-elim (off 3 2 (¬4∣ ((+ 3) - (+ 2))) h)
  phase-inj 3 3 _ _ _ = refl
  phase-inj (suc (suc (suc (suc k)))) l (s≤s (s≤s (s≤s (s≤s ())))) _ _
  phase-inj k (suc (suc (suc (suc l)))) _ (s≤s (s≤s (s≤s (s≤s ())))) _

  finish : (k l : ℕ) (x z x′ z′ : Bool) → k < 4 → l < 4 → x ≡ x′ →
           pauli ⟦ code (+ k) x z ⟧ᶜ ≈ pauli ⟦ code (+ l) x′ z′ ⟧ᶜ →
           code (+ k) x z ≡ code (+ l) x′ z′
  finish k l x z .x z′ k<4 l<4 refl e =
    cong₂ (λ m t → code (+ m) x t)
          (phase-inj k l k<4 l<4 (proj₁ (same-x (+ k) (+ l) x z z′ e)))
          (proj₂ (same-x (+ k) (+ l) x z z′ e))

-- Two Paulis with normalised codes are equal only if the codes are.

code-inj : (k l : ℕ) (x z x′ z′ : Bool) → k < 4 → l < 4 →
           pauli ⟦ code (+ k) x z ⟧ᶜ ≈ pauli ⟦ code (+ l) x′ z′ ⟧ᶜ →
           code (+ k) x z ≡ code (+ l) x′ z′
code-inj k l x z x′ z′ k<4 l<4 e =
  finish k l x z x′ z′ k<4 l<4 (x-inj (+ k) (+ l) x z x′ z′ e) e

nc-inj : (c d : Code) → pauli ⟦ nc c ⟧ᶜ ≈ pauli ⟦ nc d ⟧ᶜ → nc c ≡ nc d
nc-inj c d e =
  code-inj (cph c % (+ 4)) (cph d % (+ 4)) (cx c) (cz c) (cx d) (cz d)
           (n%d<d (cph c) (+ 4)) (n%d<d (cph d) (+ 4))
    (code≡ (code (+ (cph c % (+ 4))) (cx c) (cz c)) (nc c) refl
     ⟨≈⟩ e
     ⟨≈⟩ code≡ (nc d) (code (+ (cph d % (+ 4))) (cx d) (cz d)) refl)
