------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 8 on three qubits, decided on tries: the decision procedure,
-- the encoding preserves the semantics of every generator, and the
-- Boolean checks of the rules of Figure 8 (one per rule, over every
-- choice of indices satisfying its side conditions)
--
-- The evaluations are in Checks8/R* and Checks8/H*, not here (a few
-- thousand instances per module: Agda releases the memory of an
-- evaluation only when its module is done).  Each evaluation module
-- exports its rule pointwise, `∀ a … → (guards ⇒ decide u t) ≡ true`,
-- obtained from one `refl` on the closed conjunction by all8ₖ-true
-- with the predicate given explicitly — a predicate left to
-- unification, or a named closed conjunction compared with anything
-- else, makes Agda evaluate the whole conjunction again at every use.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Base where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; not ; if_then_else_ ; T)
open import Data.Unit using (tt)
open import Data.Bool.Properties using (∧-assoc)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; suc ; _+_ ; _∸_ ; _<_ ; _≤_ ; _<ᵇ_ ; _≡ᵇ_ ; _≤ᵇ_)
open import Data.Nat.Properties using (<⇒<ᵇ ; ≡ᵇ⇒≡ ; ≡⇒≡ᵇ ; ≤⇒≤ᵇ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (yes ; no ; ⌊_⌋)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧ ; ⟦_⟧M ; ⟦⟧-ix ; len)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (code ; parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (⟦_⟧ᴳ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Encoding

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])
import Examples.Groups.Real-Clifford+CH.BackAndForth as BackAndForth

module BF = BackAndForth 3 (0 P,_===_) ⟦_⟧ᴾ
open BF using (⟦_⟧Y)

------------------------------------------------------------------------
-- The stored reading of a word over P, and the decision

private
  ⟦_⟧GM : G.Gen 8 → Mat 3
  ⟦ g ⟧GM = matOf (proj₂ ⟦ g ⟧ᴳ)

  ⟦_⟧PM : Word (GenP 3) → Mat 3
  ⟦ [ −1−1 a b ]ʷ ⟧PM       = mulM ⟦ −1[ a ] ⟧GM ⟦ −1[ b ] ⟧GM
  ⟦ [ −1X c a b _ ]ʷ ⟧PM    = mulM ⟦ −1[ c ] ⟧GM ⟦ X[ a , b ] ⟧GM
  ⟦ [ XX a b c d _ _ ]ʷ ⟧PM = mulM ⟦ X[ a , b ] ⟧GM ⟦ X[ c , d ] ⟧GM
  ⟦ [ HH a b c d _ _ ]ʷ ⟧PM = mulM ⟦ H[ a , b ] ⟧GM ⟦ H[ c , d ] ⟧GM
  ⟦ ε ⟧PM                   = idM
  ⟦ u • t ⟧PM               = mulM ⟦ u ⟧PM ⟦ t ⟧PM

  pair-ix : (g h : G.Gen 8) → (proj₂ ⟦ g ⟧ᴳ ⊙ proj₂ ⟦ h ⟧ᴳ) ≐ ix (mulM ⟦ g ⟧GM ⟦ h ⟧GM)
  pair-ix g h = ≐-trans (⊙-cong (≐-sym (ix-matOf (proj₂ ⟦ g ⟧ᴳ))) (≐-sym (ix-matOf (proj₂ ⟦ h ⟧ᴳ)))) (≐-sym (ix-mul ⟦ g ⟧GM ⟦ h ⟧GM))

  Y-ix : (u : Word (GenP 3)) → proj₂ ⟦ u ⟧Y ≐ ix ⟦ u ⟧PM
  Y-ix [ −1−1 a b ]ʷ       = pair-ix −1[ a ] −1[ b ]
  Y-ix [ −1X c a b _ ]ʷ    = pair-ix −1[ c ] X[ a , b ]
  Y-ix [ XX a b c d _ _ ]ʷ = pair-ix X[ a , b ] X[ c , d ]
  Y-ix [ HH a b c d _ _ ]ʷ = pair-ix H[ a , b ] H[ c , d ]
  Y-ix ε                   = ≐-sym ix-id
  Y-ix (u • t)             = ≐-trans (⊙-cong (Y-ix u) (Y-ix t)) (≐-sym (ix-mul ⟦ u ⟧PM ⟦ t ⟧PM))

-- Two words over P with the same matrix, decided.
decide : Word (GenP 3) → Word (GenP 3) → Bool
decide u t = ⌊ mat-dec (scaleM (√2^ proj₁ ⟦ t ⟧Y) ⟦ u ⟧PM) (scaleM (√2^ proj₁ ⟦ u ⟧Y) ⟦ t ⟧PM) ⌋

decide-sound : (u t : Word (GenP 3)) → decide u t ≡ true → ⟦ u ⟧Y ~ ⟦ t ⟧Y
decide-sound u t eq with mat-dec (scaleM (√2^ proj₁ ⟦ t ⟧Y) ⟦ u ⟧PM) (scaleM (√2^ proj₁ ⟦ u ⟧Y) ⟦ t ⟧PM)
... | yes p =
  ≐-trans (·-cong Eq.refl (Y-ix u))
    (≐-trans (≐-sym (ix-scaleM _ _))
      (≐-trans (ix-≡ p)
        (≐-trans (ix-scaleM _ _) (·-cong Eq.refl (≐-sym (Y-ix t))))))
... | no _ with eq
...   | ()

------------------------------------------------------------------------
-- The encoding preserves the semantics of every generator

private
  by-tries : (g : Gen 3) →
             scaleM (√2^ len [ g ]ʷ) ⟦ e g ⟧PM ≡ scaleM (√2^ proj₁ ⟦ e g ⟧Y) ⟦ [ g ]ʷ ⟧M →
             ⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧
  by-tries g eq =
    ≐-trans (·-cong Eq.refl (Y-ix (e g)))
      (≐-trans (≐-sym (ix-scaleM _ _))
        (≐-trans (ix-≡ eq)
          (≐-trans (ix-scaleM _ _) (·-cong Eq.refl (≐-sym (⟦⟧-ix [ g ]ʷ))))))

e-sem₃ : (g : Gen 3) → ⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧
e-sem₃ (gate₀ ())
e-sem₃ (gate₀ () ↥)
e-sem₃ (gate₀ () ↥ ↥)
e-sem₃ (gate₀ () ↥ ↥ ↥)
e-sem₃ H-gen            = by-tries H-gen            Eq.refl
e-sem₃ Z-gen            = by-tries Z-gen            Eq.refl
e-sem₃ CZ-gen           = by-tries CZ-gen           Eq.refl
e-sem₃ CH-gen           = by-tries CH-gen           Eq.refl
e-sem₃ (H-gen ↥)        = by-tries (H-gen ↥)        Eq.refl
e-sem₃ (Z-gen ↥)        = by-tries (Z-gen ↥)        Eq.refl
e-sem₃ (CZ-gen ↥)       = by-tries (CZ-gen ↥)       Eq.refl
e-sem₃ (CH-gen ↥)       = by-tries (CH-gen ↥)       Eq.refl
e-sem₃ (H-gen ↥ ↥)      = by-tries (H-gen ↥ ↥)      Eq.refl
e-sem₃ (Z-gen ↥ ↥)      = by-tries (Z-gen ↥ ↥)      Eq.refl

------------------------------------------------------------------------
-- Every rule of Figure 8 is sound on eight basis vectors
--
-- A generic rule is decided at every choice of indices: the side
-- conditions as Booleans guard the decision, and `all8` runs over the
-- eight indices.

all8 : (Fin 8 → Bool) → Bool
all8 f = f ₀ ∧ f ₁ ∧ f ₂ ∧ f ₃ ∧ f ₄ ∧ f ₅ ∧ f ₆ ∧ f ₇

all8-true : ∀ {f} → all8 f ≡ true → ∀ i → f i ≡ true
all8-true {f} e = go (f ₀) (f ₁) (f ₂) (f ₃) (f ₄) (f ₅) (f ₆) (f ₇)
                     Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl e
  where
  go : ∀ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ →
       f ₀ ≡ b₀ → f ₁ ≡ b₁ → f ₂ ≡ b₂ → f ₃ ≡ b₃ → f ₄ ≡ b₄ → f ₅ ≡ b₅ → f ₆ ≡ b₆ → f ₇ ≡ b₇ →
       b₀ ∧ b₁ ∧ b₂ ∧ b₃ ∧ b₄ ∧ b₅ ∧ b₆ ∧ b₇ ≡ true → ∀ i → f i ≡ true
  go true true true true true true true true e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ _ ₀ = e₀
  go true true true true true true true true e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ _ ₁ = e₁
  go true true true true true true true true e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ _ ₂ = e₂
  go true true true true true true true true e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ _ ₃ = e₃
  go true true true true true true true true e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ _ ₄ = e₄
  go true true true true true true true true e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ _ ₅ = e₅
  go true true true true true true true true e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ _ ₆ = e₆
  go true true true true true true true true e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ _ ₇ = e₇
  go false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ()
  go true false _ _ _ _ _ _ _ _ _ _ _ _ _ _ ()
  go true true false _ _ _ _ _ _ _ _ _ _ _ _ _ ()
  go true true true false _ _ _ _ _ _ _ _ _ _ _ _ ()
  go true true true true false _ _ _ _ _ _ _ _ _ _ _ ()
  go true true true true true false _ _ _ _ _ _ _ _ _ _ ()
  go true true true true true true false _ _ _ _ _ _ _ _ _ ()
  go true true true true true true true false _ _ _ _ _ _ _ _ ()

∧-left : ∀ {a b} → a ∧ b ≡ true → a ≡ true
∧-left {true} _ = Eq.refl

∧-right : ∀ {a b} → a ∧ b ≡ true → b ≡ true
∧-right {true} e = e

-- A guarded decision.
infixr 2 _⇒_
_⇒_ : Bool → Bool → Bool
false ⇒ _ = true
true  ⇒ b = b

⇒-true : ∀ {a b} → (a ⇒ b) ≡ true → a ≡ true → b ≡ true
⇒-true {true} e _ = e

-- Between T b and b ≡ true.
T→true : ∀ {b} → T b → b ≡ true
T→true {true} _ = Eq.refl

true→T : ∀ {b} → b ≡ true → T b
true→T Eq.refl = tt

-- The side conditions, decided.
succᵇ : Fin 8 → Fin 8 → Bool
succᵇ a a′ = toℕ a′ ≡ᵇ suc (toℕ a)

succ-true : ∀ {a a′} → Succ a a′ → succᵇ a a′ ≡ true
succ-true {a} {a′} s = T→true (≡⇒≡ᵇ (toℕ a′) (suc (toℕ a)) s)

ltᵇ : ℕ → ℕ → Bool
ltᵇ = _<ᵇ_

lt-true : ∀ {i j} → i < j → (i <ᵇ j) ≡ true
lt-true {i} {j} p = T→true (<⇒<ᵇ p)

le-true : ∀ {i j} → i ≤ j → (i ≤ᵇ j) ≡ true
le-true {i} {j} p = T→true (≤⇒≤ᵇ p)

neqᵇ : Fin 8 → Fin 8 → Bool
neqᵇ a b = not (toℕ a ≡ᵇ toℕ b)

neq-true : ∀ {a b : Fin 8} → a ≢ b → neqᵇ a b ≡ true
neq-true {a} {b} p with toℕ a ≡ᵇ toℕ b in eq
... | true  = ⊥-elim (p (Data.Fin.Properties.toℕ-injective (≡ᵇ⇒≡ (toℕ a) (toℕ b) (true→T eq))))
  where import Data.Fin.Properties
... | false = Eq.refl

boolᵇ : Bool → Bool → Bool
boolᵇ x y = if x then y else not y

bool-true : ∀ {x y} → x ≡ y → boolᵇ x y ≡ true
bool-true {true}  Eq.refl = Eq.refl
bool-true {false} Eq.refl = Eq.refl

-- The specific words.
hh₀₁₃₂ : Word (GenP 3)
hh₀₁₃₂ = hhℕ 0 1 3 2

code₃ = code 3

------------------------------------------------------------------------
-- Conjunctions over several indices, unpacked pointwise

all8₁ : (Fin 8 → Bool) → Bool
all8₁ f = all8 f

all8₂ : (Fin 8 → Fin 8 → Bool) → Bool
all8₂ f = all8 λ a → all8 λ b → f a b

all8₃ : (Fin 8 → Fin 8 → Fin 8 → Bool) → Bool
all8₃ f = all8 λ a → all8 λ b → all8 λ c → f a b c

all8₁-true : (f : Fin 8 → Bool) → all8₁ f ≡ true → ∀ a → f a ≡ true
all8₁-true f e = all8-true e

all8₂-true : (f : Fin 8 → Fin 8 → Bool) → all8₂ f ≡ true → ∀ a b → f a b ≡ true
all8₂-true f e a b = all8-true {f = λ b → f a b} (all8-true {f = λ a → all8 λ b → f a b} e a) b

all8₃-true : (f : Fin 8 → Fin 8 → Fin 8 → Bool) → all8₃ f ≡ true → ∀ a b c → f a b c ≡ true
all8₃-true f e a b c =
  all8-true {f = λ c → f a b c}
    (all8-true {f = λ b → all8 λ c → f a b c}
      (all8-true {f = λ a → all8 λ b → all8 λ c → f a b c} e a) b) c

-- The Hadamard rules, by the pattern of the codes.
chkH′ : Maybe (ℕ × ℕ) → Fin 8 → Fin 8 → Fin 8 → Fin 8 → Bool
chkH′ (just (pb , pc)) a b c d =
  (ltᵇ pc pb ⇒ decide (hh a b c d) (W₁ (code₃ a) pc pb)) ∧
  (ltᵇ pb pc ⇒ decide (hh a b c d) (W₂ (code₃ a) pb pc))
chkH′ nothing a b c d =
  distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ d) ⇒
  decide (hh a b c d) (Σ (toℕ a) (toℕ b) (toℕ c) (toℕ d) • hh₀₁₃₂ • Σ′ (toℕ a) (toℕ b) (toℕ c) (toℕ d))
