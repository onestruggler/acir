------------------------------------------------------------------------
-- Presentations of groups
--
-- The arithmetic of the relative-phase Toffoli gate's paths
--
-- The integer, Boolean and amplitude identities that
-- PathSum.Maslov.Gate needs, apart from any circuit.  The dyadic
-- constants add up as they should: ½ + ½ is N, the numerator of 1, and
-- ¼ + ¼ = ½ (½+½, ¼+¼); the T gates contribute multiples of ⅛, and
-- 2 · ⅛ = ¼, 4 · ⅛ = ½ (two-⅛, four-T).  Modulo N, halves of bits add
-- like bits: ½a + ½b ≡ ½(a ⊕ b), since they differ by ½ · 2ab = N ab
-- (½-xor).
--
-- Along a path y₁, y₂ of the gate (y₁ the first Hadamard's variable)
-- the four T and T† gates on the target add ⅛ times a signed sum of
-- bits which is 4 x₁ x₂ y₁ - 2 x₁ x₂ (R-bracket; x₁, x₂ for the
-- controls' values), the target reads y₁ ⊕ x₁ when the second Hadamard
-- reads it (back-tᴿ), and the phase comes to
--
--    ½ x_t y₁ + ½ x₁ x₂ y₁ - ¼ x₁ x₂ + ½ (y₁ ⊕ x₁) y₂,
--
-- which modulo N is ½ y₁ (y₂ ⊕ x_t ⊕ x₁ x₂) + ½ x₁ y₂ - ¼ x₁ x₂
-- (path-phaseᴿ): y₁ occurs only in the first term.  So summing over y₁
-- gives 2 or 0 according as y₂ = x_t ⊕ x₁ x₂ (pairʳ, with the rest of
-- the phase carried along as a rotation), of the two values of y₂ one
-- survives (outerʳ), and what remains of the phase there,
-- ½ x₁ (x_t ⊕ x₁ x₂) - ¼ x₁ x₂, is ½ x₁ x_t + ¼ x₁ x₂ modulo N
-- (survive).  That relative phase at x and at the Toffoli image of x
-- add up to 0 modulo N (cancelᴿ).
--
-- Every Boolean identity is proved by cases, the integer ones by the
-- laws of ℤ with ⅛, ¼ and ½ symbolic.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Maslov.Arith (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _xor_)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (divides)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-inverseˡ; +-comm; +-assoc; *-identityʳ;
   *-zeroʳ; *-assoc; *-distribʳ-+)
open import Data.Integer.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Compose.Sum M₀ using (zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; -ᴬ_; _·ᴬ_; _≐_; zpow; zpow-anti; N)
open import PathSum.Order M using (pow-suc)
open import PathSum.Reduction M using (⅛; ¼; ½)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; mod-N; ≡ᴺ-refl; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ--; module ≡ᴺ-Reasoning)
open import PathSum.Toffoli.Arith M₀ using (four-T)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)
open ≡ᴺ-Reasoning


------------------------------------------------------------------------
-- The dyadic constants

private
  double : ∀ a → a + a ≡ a * (+ 2)
  double = solve 1 (λ a → a :+ a := a :* con (+ 2)) refl

-- ½ + ½ = 1 and ¼ + ¼ = ½, as numerators over N (N and pow M are the
-- same number, 2^M).

½+½ : ½ + ½ ≡ + N
½+½ = trans (double ½) (sym (pow-suc (suc (suc M₀))))

¼+¼ : ¼ + ¼ ≡ ½
¼+¼ = trans (double ¼) (sym (pow-suc (suc M₀)))

½·2 : ½ * (+ 2) ≡ + N
½·2 = sym (pow-suc (suc (suc M₀)))

-- The T gates' multiples of ⅛: 2 · ⅛ = ¼ (and 4 · ⅛ = ½ is
-- PathSum.Toffoli.Arith.four-T).

two-⅛ : ∀ s → ⅛ * ((+ 2) * s) ≡ ¼ * s
two-⅛ s = trans (sym (*-assoc ⅛ (+ 2) s)) (cong (_* s) (sym (pow-suc M₀)))

¼+¼·c : ∀ s → ¼ * s + ¼ * s ≡ ½ * s
¼+¼·c s = trans (sym (*-distribʳ-+ s ¼ ¼)) (cong (_* s) ¼+¼)


------------------------------------------------------------------------
-- Halves modulo 1

private
  factor : ∀ h p q s → h * p + h * q - h * s ≡ h * (p + q - s)
  factor = solve 4 (λ h p q s →
    h :* p :+ h :* q :- h :* s := h :* (p :+ q :- s)) refl

  swap : ∀ h k → h * ((+ 2) * k) ≡ k * (h * (+ 2))
  swap = solve 2 (λ h k → h :* (con (+ 2) :* k) := k :* (h :* con (+ 2)))
                 refl

  bits2 : ∀ a b → [ a ]ᶻ + [ b ]ᶻ - [ a xor b ]ᶻ ≡ (+ 2) * [ a ∧ b ]ᶻ
  bits2 true  true  = refl
  bits2 true  false = refl
  bits2 false true  = refl
  bits2 false false = refl

  xor-same : ∀ a → a xor a ≡ false
  xor-same true  = refl
  xor-same false = refl

-- ½a + ½b and ½(a ⊕ b) differ by ½ · 2ab = N ab.

½-xor : ∀ a b → ½ * [ a ]ᶻ + ½ * [ b ]ᶻ ≡ᴺ ½ * [ a xor b ]ᶻ
½-xor a b = mod-N (divides [ a ∧ b ]ᶻ
  (trans (factor ½ [ a ]ᶻ [ b ]ᶻ [ a xor b ]ᶻ)
    (trans (cong (½ *_) (bits2 a b))
      (trans (swap ½ [ a ∧ b ]ᶻ) (cong ([ a ∧ b ]ᶻ *_) ½·2)))))

-- So ½a + ½a is 0.

½-self : ∀ a → ½ * [ a ]ᶻ + ½ * [ a ]ᶻ ≡ᴺ 0ℤ
½-self a = begin
  ½ * [ a ]ᶻ + ½ * [ a ]ᶻ ≡ᴺ⟨ ½-xor a a ⟩
  ½ * [ a xor a ]ᶻ         ≡⟨ cong (λ b → ½ * [ b ]ᶻ) (xor-same a) ⟩
  ½ * 0ℤ                   ≡⟨ *-zeroʳ ½ ⟩
  0ℤ                       ∎


------------------------------------------------------------------------
-- The phase of a path

-- The four T and T† gates on the target add ⅛ times this signed sum
-- of the target's values, b being the first Hadamard's variable.

R-bracket : ∀ b x₁ x₂ →
  [ b ]ᶻ - [ b xor x₂ ]ᶻ + [ (b xor x₂) xor x₁ ]ᶻ
  - [ ((b xor x₂) xor x₁) xor x₂ ]ᶻ
  ≡ (+ 4) * [ (x₁ ∧ x₂) ∧ b ]ᶻ - (+ 2) * [ x₁ ∧ x₂ ]ᶻ
R-bracket true  true  true  = refl
R-bracket true  true  false = refl
R-bracket true  false true  = refl
R-bracket true  false false = refl
R-bracket false true  true  = refl
R-bracket false true  false = refl
R-bracket false false true  = refl
R-bracket false false false = refl

-- After the three CNOTs the target reads b ⊕ x₁.

back-tᴿ : ∀ b x₁ x₂ → ((b xor x₂) xor x₁) xor x₂ ≡ b xor x₁
back-tᴿ true  true  true  = refl
back-tᴿ true  true  false = refl
back-tᴿ true  false true  = refl
back-tᴿ true  false false = refl
back-tᴿ false true  true  = refl
back-tᴿ false true  false = refl
back-tᴿ false false true  = refl
back-tᴿ false false false = refl

-- The phase along a path, tidied: the two Hadamards' terms and ⅛ times
-- the signed sum; then ⅛ (4B - 2C) = ½B - ¼C.

tidyᴿ : ∀ h t p q e₁ e₂ e₃ e₄ →
  0ℤ + h * p + t * e₁ - t * e₂ + t * e₃ - t * e₄ + h * q
  ≡ h * p + h * q + t * (e₁ - e₂ + e₃ - e₄)
tidyᴿ = solve 8 (λ h t p q e₁ e₂ e₃ e₄ →
  con 0ℤ :+ h :* p :+ t :* e₁ :- t :* e₂ :+ t :* e₃ :- t :* e₄ :+ h :* q
  := h :* p :+ h :* q :+ t :* (e₁ :- e₂ :+ e₃ :- e₄)) refl

⅛-split : ∀ B C → ⅛ * ((+ 4) * B - (+ 2) * C) ≡ ½ * B - ¼ * C
⅛-split B C =
  trans (distrib ⅛ ((+ 4) * B) ((+ 2) * C))
        (cong₂ _-_ (four-T B) (two-⅛ C))
  where
  distrib : ∀ t u v → t * (u - v) ≡ t * u - t * v
  distrib = solve 3 (λ t u v → t :* (u :- v) := t :* u :- t :* v) refl

arrange : ∀ a q b c → a + q + (b - c) ≡ a + b - c + q
arrange = solve 4 (λ a q b c → a :+ q :+ (b :- c) := a :+ b :- c :+ q) refl

-- The phase bit: x_t y₁ ⊕ x₁ x₂ y₁ ⊕ (y₁ ⊕ x₁) y₂ is
-- y₁ (y₂ ⊕ x_t ⊕ x₁ x₂) ⊕ x₁ y₂.

phase-bitᴿ : ∀ xt x₁ x₂ y₁ y₂ →
  ((xt ∧ y₁) xor ((x₁ ∧ x₂) ∧ y₁)) xor ((y₁ xor x₁) ∧ y₂) ≡
  (y₁ ∧ (y₂ xor (xt xor (x₁ ∧ x₂)))) xor (x₁ ∧ y₂)
phase-bitᴿ true  true  true  true  true  = refl
phase-bitᴿ true  true  true  true  false = refl
phase-bitᴿ true  true  true  false true  = refl
phase-bitᴿ true  true  true  false false = refl
phase-bitᴿ true  true  false true  true  = refl
phase-bitᴿ true  true  false true  false = refl
phase-bitᴿ true  true  false false true  = refl
phase-bitᴿ true  true  false false false = refl
phase-bitᴿ true  false true  true  true  = refl
phase-bitᴿ true  false true  true  false = refl
phase-bitᴿ true  false true  false true  = refl
phase-bitᴿ true  false true  false false = refl
phase-bitᴿ true  false false true  true  = refl
phase-bitᴿ true  false false true  false = refl
phase-bitᴿ true  false false false true  = refl
phase-bitᴿ true  false false false false = refl
phase-bitᴿ false true  true  true  true  = refl
phase-bitᴿ false true  true  true  false = refl
phase-bitᴿ false true  true  false true  = refl
phase-bitᴿ false true  true  false false = refl
phase-bitᴿ false true  false true  true  = refl
phase-bitᴿ false true  false true  false = refl
phase-bitᴿ false true  false false true  = refl
phase-bitᴿ false true  false false false = refl
phase-bitᴿ false false true  true  true  = refl
phase-bitᴿ false false true  true  false = refl
phase-bitᴿ false false true  false true  = refl
phase-bitᴿ false false true  false false = refl
phase-bitᴿ false false false true  true  = refl
phase-bitᴿ false false false true  false = refl
phase-bitᴿ false false false false true  = refl
phase-bitᴿ false false false false false = refl

-- Modulo N the phase along the path y₁, y₂ is
-- ½ y₁ (y₂ ⊕ x_t ⊕ x₁ x₂) + (½ x₁ y₂ - ¼ x₁ x₂).

path-phaseᴿ : ∀ xt x₁ x₂ y₁ y₂ →
  ½ * [ xt ∧ y₁ ]ᶻ + ½ * [ (x₁ ∧ x₂) ∧ y₁ ]ᶻ - ¼ * [ x₁ ∧ x₂ ]ᶻ
  + ½ * [ (y₁ xor x₁) ∧ y₂ ]ᶻ
  ≡ᴺ ½ * [ y₁ ∧ (y₂ xor (xt xor (x₁ ∧ x₂))) ]ᶻ
     + (½ * [ x₁ ∧ y₂ ]ᶻ - ¼ * [ x₁ ∧ x₂ ]ᶻ)
path-phaseᴿ xt x₁ x₂ y₁ y₂ = begin
  ½ * [ a ]ᶻ + ½ * [ b ]ᶻ - ¼ * [ c ]ᶻ + ½ * [ d ]ᶻ
    ≡⟨ rearr (½ * [ a ]ᶻ) (½ * [ b ]ᶻ) (¼ * [ c ]ᶻ) (½ * [ d ]ᶻ) ⟩
  ½ * [ a ]ᶻ + ½ * [ b ]ᶻ + ½ * [ d ]ᶻ - ¼ * [ c ]ᶻ
    ≡ᴺ⟨ ≡ᴺ-- (≡ᴺ-trans (≡ᴺ-+ (½-xor a b) (≡ᴺ-refl {½ * [ d ]ᶻ}))
                        (½-xor (a xor b) d))
             (≡ᴺ-refl {¼ * [ c ]ᶻ}) ⟩
  ½ * [ (a xor b) xor d ]ᶻ - ¼ * [ c ]ᶻ
    ≡⟨ cong (λ e → ½ * [ e ]ᶻ - ¼ * [ c ]ᶻ) (phase-bitᴿ xt x₁ x₂ y₁ y₂) ⟩
  ½ * [ P xor Q ]ᶻ - ¼ * [ c ]ᶻ
    ≡ᴺ⟨ ≡ᴺ-- (≡ᴺ-sym (½-xor P Q)) (≡ᴺ-refl {¼ * [ c ]ᶻ}) ⟩
  ½ * [ P ]ᶻ + ½ * [ Q ]ᶻ - ¼ * [ c ]ᶻ
    ≡⟨ +-assoc (½ * [ P ]ᶻ) (½ * [ Q ]ᶻ) (- (¼ * [ c ]ᶻ)) ⟩
  ½ * [ P ]ᶻ + (½ * [ Q ]ᶻ - ¼ * [ c ]ᶻ) ∎
  where
  a b c d P Q : Bool
  a = xt ∧ y₁
  b = (x₁ ∧ x₂) ∧ y₁
  c = x₁ ∧ x₂
  d = (y₁ xor x₁) ∧ y₂
  P = y₁ ∧ (y₂ xor (xt xor (x₁ ∧ x₂)))
  Q = x₁ ∧ y₂

  rearr : ∀ w u v s → w + u - v + s ≡ w + u + s - v
  rearr = solve 4 (λ w u v s → w :+ u :- v :+ s := w :+ u :+ s :- v) refl


------------------------------------------------------------------------
-- The relative phase

private
  ∧-xor : ∀ a b c → a ∧ (b xor (a ∧ c)) ≡ (a ∧ b) xor (a ∧ c)
  ∧-xor true  b c = refl
  ∧-xor false b c = refl

  twice : ∀ a b c → (a ∧ b) xor (a ∧ (b xor (a ∧ c))) ≡ a ∧ c
  twice true  true  true  = refl
  twice true  true  false = refl
  twice true  false true  = refl
  twice true  false false = refl
  twice false true  true  = refl
  twice false true  false = refl
  twice false false true  = refl
  twice false false false = refl

  halves : ∀ A s → A + ½ * s - ¼ * s ≡ A + ¼ * s + 0ℤ
  halves A s = trans (cong (λ h → A + h - ¼ * s) (sym (¼+¼·c s)))
    (solve 3 (λ A q s → A :+ (q :* s :+ q :* s) :- q :* s
                        := A :+ q :* s :+ con 0ℤ) refl A ¼ s)

-- What survives of the phase, ½ x₁ (x_t ⊕ x₁ x₂) - ¼ x₁ x₂, is
-- ½ x₁ x_t + ¼ x₁ x₂ (plus the 0 of the basis column's own phase).

survive : ∀ xt x₁ x₂ →
  ½ * [ x₁ ∧ (xt xor (x₁ ∧ x₂)) ]ᶻ - ¼ * [ x₁ ∧ x₂ ]ᶻ
  ≡ᴺ ½ * [ x₁ ∧ xt ]ᶻ + ¼ * [ x₁ ∧ x₂ ]ᶻ + 0ℤ
survive xt x₁ x₂ = begin
  ½ * [ x₁ ∧ (xt xor (x₁ ∧ x₂)) ]ᶻ - ¼ * [ x₁ ∧ x₂ ]ᶻ
    ≡⟨ cong (λ e → ½ * [ e ]ᶻ - ¼ * [ x₁ ∧ x₂ ]ᶻ) (∧-xor x₁ xt x₂) ⟩
  ½ * [ (x₁ ∧ xt) xor (x₁ ∧ x₂) ]ᶻ - ¼ * [ x₁ ∧ x₂ ]ᶻ
    ≡ᴺ⟨ ≡ᴺ-- (≡ᴺ-sym (½-xor (x₁ ∧ xt) (x₁ ∧ x₂)))
             (≡ᴺ-refl {¼ * [ x₁ ∧ x₂ ]ᶻ}) ⟩
  ½ * [ x₁ ∧ xt ]ᶻ + ½ * [ x₁ ∧ x₂ ]ᶻ - ¼ * [ x₁ ∧ x₂ ]ᶻ
    ≡⟨ halves (½ * [ x₁ ∧ xt ]ᶻ) [ x₁ ∧ x₂ ]ᶻ ⟩
  ½ * [ x₁ ∧ xt ]ᶻ + ¼ * [ x₁ ∧ x₂ ]ᶻ + 0ℤ ∎

-- The relative phase at x plus the relative phase at the Toffoli image
-- of x (whose target reads x_t ⊕ x₁ x₂) is 0 modulo N:
-- ½ x₁ x_t + ½ x₁ (x_t ⊕ x₁ x₂) ≡ ½ x₁ x₂, and ¼ + ¼ = ½.

cancelᴿ : ∀ xt x₁ x₂ →
  (½ * [ x₁ ∧ xt ]ᶻ + ¼ * [ x₁ ∧ x₂ ]ᶻ)
  + (½ * [ x₁ ∧ (xt xor (x₁ ∧ x₂)) ]ᶻ + ¼ * [ x₁ ∧ x₂ ]ᶻ) ≡ᴺ 0ℤ
cancelᴿ xt x₁ x₂ = begin
  (½ * [ a ]ᶻ + ¼ * [ c ]ᶻ) + (½ * [ b ]ᶻ + ¼ * [ c ]ᶻ)
    ≡⟨ regroup (½ * [ a ]ᶻ) (½ * [ b ]ᶻ) (¼ * [ c ]ᶻ) ⟩
  (½ * [ a ]ᶻ + ½ * [ b ]ᶻ) + (¼ * [ c ]ᶻ + ¼ * [ c ]ᶻ)
    ≡⟨ cong (λ u → (½ * [ a ]ᶻ + ½ * [ b ]ᶻ) + u) (¼+¼·c [ c ]ᶻ) ⟩
  (½ * [ a ]ᶻ + ½ * [ b ]ᶻ) + ½ * [ c ]ᶻ
    ≡ᴺ⟨ ≡ᴺ-+ (½-xor a b) (≡ᴺ-refl {½ * [ c ]ᶻ}) ⟩
  ½ * [ a xor b ]ᶻ + ½ * [ c ]ᶻ
    ≡⟨ cong (λ e → ½ * [ e ]ᶻ + ½ * [ c ]ᶻ) (twice x₁ xt x₂) ⟩
  ½ * [ c ]ᶻ + ½ * [ c ]ᶻ
    ≡ᴺ⟨ ½-self c ⟩
  0ℤ ∎
  where
  a b c : Bool
  a = x₁ ∧ xt
  b = x₁ ∧ (xt xor (x₁ ∧ x₂))
  c = x₁ ∧ x₂

  regroup : ∀ p q u → (p + u) + (q + u) ≡ (p + q) + (u + u)
  regroup = solve 3 (λ p q u → (p :+ u) :+ (q :+ u) := (p :+ q) :+ (u :+ u))
                    refl


------------------------------------------------------------------------
-- Summing two path variables

-- 2 ζ^e.

twoᶻ : ℤ → Amp
twoᶻ e = (+ 2) ·ᴬ zpow e

private
  zpow-½0 : ∀ e → zpow (½ * [ false ]ᶻ + e) ≐ zpow e
  zpow-½0 e = zpow-≡ (trans (cong (_+ e) (*-zeroʳ ½)) (+-identityˡ e))

  zpow-½1 : ∀ e → zpow (½ * [ true ]ᶻ + e) ≐ -ᴬ zpow e
  zpow-½1 e i = trans (zpow-≡ (trans (cong (_+ e) (*-identityʳ ½))
                                     (+-comm ½ e)) i)
                      (zpow-anti e i)

  double′ : ∀ a → a + a ≡ (+ 2) * a
  double′ = solve 1 (λ a → a :+ a := con (+ 2) :* a) refl

-- For one value of y₂, the two values of y₁, the rest e of the phase
-- carried along: ζ^e (1 + (-1)^q).

pairʳ : ∀ s q e →
        ((if s then zpow (½ * [ q ]ᶻ + e) else 0ᴬ) +ᴬ
         (if s then zpow (½ * [ false ]ᶻ + e) else 0ᴬ)) ≐
        (if s then (if q then 0ᴬ else twoᶻ e) else 0ᴬ)
pairʳ false q     e i = refl
pairʳ true  false e i =
  trans (cong₂ _+_ (zpow-½0 e i) (zpow-½0 e i)) (double′ (zpow e i))
pairʳ true  true  e i =
  trans (cong₂ _+_ (zpow-½1 e i) (zpow-½0 e i)) (+-inverseˡ (zpow e i))

-- Then the two values of y₂: only y₂ = r survives, with its own rest of
-- the phase.

outerʳ : ∀ r sT sF eT eF →
         ((if sT then (if not r then 0ᴬ else twoᶻ eT) else 0ᴬ) +ᴬ
          (if sF then (if r then 0ᴬ else twoᶻ eF) else 0ᴬ)) ≐
         (+ 2) ·ᴬ (if (if r then sT else sF)
                   then zpow (if r then eT else eF) else 0ᴬ)
outerʳ true  true  true  eT eF i = +-identityʳ (twoᶻ eT i)
outerʳ true  true  false eT eF i = +-identityʳ (twoᶻ eT i)
outerʳ true  false true  eT eF i = refl
outerʳ true  false false eT eF i = refl
outerʳ false true  true  eT eF i = +-identityˡ (twoᶻ eF i)
outerʳ false false true  eT eF i = +-identityˡ (twoᶻ eF i)
outerʳ false true  false eT eF i = refl
outerʳ false false false eT eF i = refl

select-if : {A : Set} (s : Bool → A) (r : Bool) →
            (if r then s true else s false) ≡ s r
select-if s true  = refl
select-if s false = refl
