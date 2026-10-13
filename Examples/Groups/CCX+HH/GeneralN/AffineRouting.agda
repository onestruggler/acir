------------------------------------------------------------------------
-- Presentations of groups
--
-- Elementary affine routing of three distinct basis assignments.
-- Translation sends the first to zero.  A recursive CX/SWAP reduction
-- sends the second to e₀.  Reducing the remaining tail and clearing
-- its first bit sends the third to e₁ while fixing zero and e₀.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.AffineRouting where

open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)
open import Relation.Nullary.Negation using (¬_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH.GeneralN.Classical
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons)

private variable n : ℕ

data NZ : ℕ → Set where
  one : NZ (suc n)
  both next : NZ (suc n) → NZ (suc (suc n))

vec : NZ n → State n
vec one = e₀
vec (both v) = cons true (vec v)
vec (next v) = cons false (vec v)

reduce : NZ n → Circuit n
reduce one = ε
reduce (both v) = CX₀₁ • (reduce v ↑)
reduce (next v) = [ gate₂ SWAP-gate ]ʷ • (reduce v ↑)

private
  cx01-zero : ∀ {n} → act (CX₀₁ {n}) zeros ≈s zeros
  cx01-zero zero = refl
  cx01-zero (suc zero) = refl
  cx01-zero (suc (suc i)) = refl

  swap-zero : ∀ {n} → act [ gate₂ {n} SWAP-gate ]ʷ zeros ≈s zeros
  swap-zero zero = refl
  swap-zero (suc zero) = refl
  swap-zero (suc (suc i)) = refl

  cx01-both : ∀ {n} → act (CX₀₁ {n}) (cons true e₀) ≈s e₀
  cx01-both zero = refl
  cx01-both (suc zero) = refl
  cx01-both (suc (suc i)) = refl

  swap-next : ∀ {n} → act [ gate₂ {n} SWAP-gate ]ʷ (cons false e₀) ≈s e₀
  swap-next zero = refl
  swap-next (suc zero) = refl
  swap-next (suc (suc i)) = refl

reduce-zero : ∀ (v : NZ n) → act (reduce v) zeros ≈s zeros
reduce-zero one i = refl
reduce-zero (both v) i = trans (act-cong CX₀₁ lifted i) (cx01-zero i)
  where
  lifted : act (reduce v ↑) zeros ≈s zeros
  lifted zero = shift-correct (reduce v) zeros zero
  lifted (suc j) = trans (shift-correct (reduce v) zeros (suc j)) (reduce-zero v j)
reduce-zero (next v) i = trans (act-cong [ gate₂ SWAP-gate ]ʷ lifted i) (swap-zero i)
  where
  lifted : act (reduce v ↑) zeros ≈s zeros
  lifted zero = shift-correct (reduce v) zeros zero
  lifted (suc j) = trans (shift-correct (reduce v) zeros (suc j)) (reduce-zero v j)

reduce-vec : ∀ (v : NZ (suc n)) → act (reduce v) (vec v) ≈s e₀
reduce-vec one i = refl
reduce-vec (both v) i = trans (act-cong CX₀₁ lifted i) (cx01-both i)
  where
  lifted : act (reduce v ↑) (cons true (vec v)) ≈s cons true e₀
  lifted j = trans (act-up-cons (reduce v) true (vec v) j) (cons-cong refl (reduce-vec v) j)
reduce-vec (next v) i = trans (act-cong [ gate₂ SWAP-gate ]ʷ lifted i) (swap-next i)
  where
  lifted : act (reduce v ↑) (cons false (vec v)) ≈s cons false e₀
  lifted j = trans (act-up-cons (reduce v) false (vec v) j) (cons-cong refl (reduce-vec v) j)

data View (s : State n) : Set where
  is-zero : s ≈s zeros → View s
  is-nonzero : (v : NZ n) → vec v ≈s s → View s

private
  view-cong : ∀ {s t : State n} → s ≈s t → View s → View t
  view-cong eq (is-zero z) = is-zero λ i → trans (sym (eq i)) (z i)
  view-cong eq (is-nonzero v vs) = is-nonzero v λ i → trans (vs i) (eq i)

  view-cons : ∀ b (s : State n) → View s → View (cons b s)
  view-cons false s (is-zero z) = is-zero λ { zero → refl ; (suc i) → z i }
  view-cons true s (is-zero z) = is-nonzero one λ
    { zero → refl ; (suc i) → sym (z i) }
  view-cons {zero} b s (is-nonzero () eq)
  view-cons {suc n} false s (is-nonzero v vs) = is-nonzero (next v) (cons-cong refl vs)
  view-cons {suc n} true s (is-nonzero v vs) = is-nonzero (both v) (cons-cong refl vs)

view : ∀ n (s : State n) → View s
view zero s = is-zero λ ()
view (suc n) s = view-cong (cons-view s) (view-cons (s zero) (lower s) (view n (lower s)))

nonzero : ∀ n (s : State n) → ¬ (s ≈s zeros) → Σ (NZ n) (λ v → vec v ≈s s)
nonzero n s nz = choose (view n s)
  where
  choose : View s → Σ (NZ n) (λ v → vec v ≈s s)
  choose (is-zero eq) = ⊥-elim (nz eq)
  choose (is-nonzero v eq) = v , eq

record Reduction (s : State (suc n)) : Set where
  field
    word : Circuit (suc n)
    zero-fixed : act word zeros ≈s zeros
    to-first : act word s ≈s e₀
open Reduction public

reduction : ∀ (s : State (suc n)) → ¬ (s ≈s zeros) → Reduction s
reduction {n} s nz = record
  { word = reduce v
  ; zero-fixed = reduce-zero v
  ; to-first = λ i → trans (act-cong (reduce v) (λ j → sym (vs j)) i) (reduce-vec v i)
  }
  where
  v = proj₁ (nonzero (suc n) s nz)
  vs = proj₂ (nonzero (suc n) s nz)

private
  tail-nonzero : ∀ (s : State (suc n)) → ¬ (s ≈s zeros) → ¬ (s ≈s e₀) →
    ¬ (lower s ≈s zeros)
  tail-nonzero s nz ne tailzero = decide (s zero) refl
    where
    decide : ∀ b → s zero ≡ b → ⊥
    decide false eq = nz λ { zero → eq ; (suc i) → tailzero i }
    decide true eq = ne λ { zero → eq ; (suc i) → tailzero i }

  clear : Bool → Circuit (suc (suc n))
  clear false = ε
  clear true = [ gate₂ CX-gate ]ʷ

  clear-zero : ∀ b → act (clear {n} b) zeros ≈s zeros
  clear-zero false i = refl
  clear-zero true zero = refl
  clear-zero true (suc i) = refl

  clear-first : ∀ b → act (clear {n} b) e₀ ≈s e₀
  clear-first false i = refl
  clear-first true zero = refl
  clear-first true (suc i) = refl

  clear-tail : ∀ b → act (clear {n} b) (cons b e₀) ≈s e₁
  clear-tail false zero = refl
  clear-tail false (suc zero) = refl
  clear-tail false (suc (suc i)) = refl
  clear-tail true zero = refl
  clear-tail true (suc zero) = refl
  clear-tail true (suc (suc i)) = refl

record TailReduction (s : State (suc (suc n))) : Set where
  field
    word : Circuit (suc (suc n))
    zero-fixed : act word zeros ≈s zeros
    first-fixed : act word e₀ ≈s e₀
    to-second : act word s ≈s e₁
open TailReduction public

tail-reduction : ∀ (s : State (suc (suc n))) → ¬ (s ≈s zeros) → ¬ (s ≈s e₀) → TailReduction s
tail-reduction s nz ne = record
  { word = clear (s zero) • (Reduction.word r ↑)
  ; zero-fixed = λ i → trans (act-cong (clear (s zero)) lifted-zero i) (clear-zero (s zero) i)
  ; first-fixed = λ i → trans (act-cong (clear (s zero)) lifted-first i) (clear-first (s zero) i)
  ; to-second = λ i → trans (act-cong (clear (s zero)) lifted-target i) (clear-tail (s zero) i)
  }
  where
  r = reduction (lower s) (tail-nonzero s nz ne)

  lifted-zero : act (Reduction.word r ↑) zeros ≈s zeros
  lifted-zero zero = shift-correct (Reduction.word r) zeros zero
  lifted-zero (suc i) = trans (shift-correct (Reduction.word r) zeros (suc i)) (Reduction.zero-fixed r i)

  lifted-first : act (Reduction.word r ↑) e₀ ≈s e₀
  lifted-first zero = shift-correct (Reduction.word r) e₀ zero
  lifted-first (suc i) = trans (shift-correct (Reduction.word r) e₀ (suc i)) (Reduction.zero-fixed r i)

  lifted-target : act (Reduction.word r ↑) s ≈s cons (s zero) e₀
  lifted-target zero = shift-correct (Reduction.word r) s zero
  lifted-target (suc i) = trans (shift-correct (Reduction.word r) s (suc i)) (Reduction.to-first r i)

record TripleRoute (a b c : State (suc (suc n))) : Set where
  field
    word : Circuit (suc (suc n))
    first : act word a ≈s zeros
    second : act word b ≈s e₀
    third : act word c ≈s e₁
open TripleRoute public

triple-route : ∀ (a b c : State (suc (suc n))) →
  ¬ (a ≈s b) → ¬ (a ≈s c) → ¬ (b ≈s c) → TripleRoute a b c
triple-route {n} a b c ab ac bc = record
  { word = TailReduction.word r₂ • q
  ; first = λ i → trans (act-cong (TailReduction.word r₂) qa i) (TailReduction.zero-fixed r₂ i)
  ; second = λ i → trans (act-cong (TailReduction.word r₂) qb i) (TailReduction.first-fixed r₂ i)
  ; third = TailReduction.to-second r₂
  }
  where
  tr = translate (suc (suc n)) a

  translated-b-nz : ¬ (act tr b ≈s zeros)
  translated-b-nz eq = ab (act-injective tr λ i → trans (translate-self _ a i) (sym (eq i)))

  r₁ = reduction (act tr b) translated-b-nz
  q = Reduction.word r₁ • tr

  qa : act q a ≈s zeros
  qa i = trans (act-cong (Reduction.word r₁) (translate-self _ a) i) (Reduction.zero-fixed r₁ i)

  qb : act q b ≈s e₀
  qb = Reduction.to-first r₁

  c-nz : ¬ (act q c ≈s zeros)
  c-nz eq = ac (act-injective q λ i → trans (qa i) (sym (eq i)))

  c-ne : ¬ (act q c ≈s e₀)
  c-ne eq = bc (act-injective q λ i → trans (qb i) (sym (eq i)))

  r₂ = tail-reduction (act q c) c-nz c-ne
