------------------------------------------------------------------------
-- Presentations of groups
--
-- Five points of five bits lie on an affine hyperplane
--
-- A rule of P′ has at most five indices, read on five wires as five
-- bit vectors v₀ … v₄.  The map c ↦ (c · (vᵢ ⊕ v₀))ᵢ sends the 32
-- vectors c to 16 values, so two of them, c₁ ≠ c₂, agree (stdlib's
-- pigeonhole), and c = c₁ ⊕ c₂ ≠ 0 has c · vᵢ = c · v₀ for every i
-- (`hyper`).  The affine circuit `βc c κ` then reads c · x ⊕ κ on the
-- top wire (`β-top`): it sends the hyperplane c · x = κ into the half
-- where the top wire is 0.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Hyper where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; _∧_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; _<_)
open import Data.Fin.Properties using (pigeonhole ; <⇒≢)
open import Data.Nat using (ℕ ; _<?_) renaming (_<_ to _<ℕ_)
open import Data.Nat.Primality using (prime[2])
open import Data.Product using (_,_ ; Σ ; _×_)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary.Decidable using (toWitness)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics using (Bits)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm)
open import Examples.Groups.Clifford+CS.Five.Sem.Build
  using (ze ; _⊕ᵥ_ ; dot ; ⊕-ze ; Xb ; bm-Xb ; rowB ; bm-rowB)

import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
import Examples.Groups.Clifford+CS.Numbering 5 as N5
import Examples.Groups.Clifford+CS.Numbering 4 as N4

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Linearity of the dot product

private
  shuffle : ∀ p q r s → (p xor q) xor (r xor s) ≡ (p xor r) xor (q xor s)
  shuffle false false false false = refl
  shuffle false false false true  = refl
  shuffle false false true  false = refl
  shuffle false false true  true  = refl
  shuffle false true  false false = refl
  shuffle false true  false true  = refl
  shuffle false true  true  false = refl
  shuffle false true  true  true  = refl
  shuffle true  false false false = refl
  shuffle true  false false true  = refl
  shuffle true  false true  false = refl
  shuffle true  false true  true  = refl
  shuffle true  true  false false = refl
  shuffle true  true  false true  = refl
  shuffle true  true  true  false = refl
  shuffle true  true  true  true  = refl

dot-⊕ˡ : (a b x : Bits n) → dot (a ⊕ᵥ b) x ≡ dot a x xor dot b x
dot-⊕ˡ []      []      []      = refl
dot-⊕ˡ (a ∷ as) (b ∷ bs) (x ∷ xs) =
  Eq.trans (Eq.cong₂ _xor_ (BoolP.∧-distribʳ-xor x a b) (dot-⊕ˡ as bs xs))
    (shuffle (a ∧ x) (b ∧ x) (dot as xs) (dot bs xs))

dot-⊕ʳ : (c x y : Bits n) → dot c (x ⊕ᵥ y) ≡ dot c x xor dot c y
dot-⊕ʳ []       []       []       = refl
dot-⊕ʳ (c ∷ cs) (x ∷ xs) (y ∷ ys) =
  Eq.trans (Eq.cong₂ _xor_ (BoolP.∧-distribˡ-xor c x y) (dot-⊕ʳ cs xs ys))
    (shuffle (c ∧ x) (c ∧ y) (dot cs xs) (dot cs ys))

⊕-cancelʳ : (x y : Bits n) → (x ⊕ᵥ y) ⊕ᵥ y ≡ x
⊕-cancelʳ []       []       = refl
⊕-cancelʳ (a ∷ xs) (b ∷ ys) =
  Eq.cong₂ _∷_ (Eq.trans (BoolP.xor-assoc a b b) (Eq.trans (Eq.cong (a xor_) (BoolP.xor-same b)) (BoolP.xor-identityʳ a)))
               (⊕-cancelʳ xs ys)

------------------------------------------------------------------------
-- The hyperplane

record Plane (v : Vec (Bits 5) 5) : Set where
  field
    c  : Bits 5
    nz : c ≢ ze
    on : ∀ i → dot c (lookup v i) ≡ dot c (lookup v zero)

hyper : (v : Vec (Bits 5) 5) → Plane v
hyper v = go (pigeonhole lt f)
  where
  v₀ : Bits 5
  v₀ = lookup v zero

  d : Fin 4 → Bits 5
  d i = lookup v (suc i) ⊕ᵥ v₀

  sig : Bits 5 → Bits 4
  sig c = tabulate (λ i → dot c (d i))

  f : Fin N5.N → Fin N4.N
  f k = N4.idx (sig (N5.cod k))

  lt : N4.N <ℕ N5.N
  lt = toWitness {a? = N4.N <? N5.N} _

  go : (Σ (Fin N5.N) λ i → Σ (Fin N5.N) λ j → i < j × f i ≡ f j) → Plane v
  go (i , j , i<j , e) = record { c = c ; nz = nz ; on = on }
    where
    c : Bits 5
    c = N5.cod i ⊕ᵥ N5.cod j

    nz : c ≢ ze
    nz h = <⇒≢ i<j (N5.cod-inj {i} {j} (⊕-ze (N5.cod i) (N5.cod j) h))

    same : ∀ k → dot (N5.cod i) (d k) ≡ dot (N5.cod j) (d k)
    same k = Eq.trans (Eq.sym (lookup∘tabulate (λ k → dot (N5.cod i) (d k)) k))
               (Eq.trans (Eq.cong (λ t → lookup t k) (N4.idx-inj {sig (N5.cod i)} {sig (N5.cod j)} e))
                 (lookup∘tabulate (λ k → dot (N5.cod j) (d k)) k))

    on : ∀ k → dot c (lookup v k) ≡ dot c v₀
    on zero    = refl
    on (suc k) =
      Eq.trans (Eq.cong (dot c) (Eq.sym (⊕-cancelʳ (lookup v (suc k)) v₀)))
        (Eq.trans (dot-⊕ʳ c (d k) v₀)
          (Eq.cong (_xor dot c v₀)
            (Eq.trans (dot-⊕ˡ (N5.cod i) (N5.cod j) (d k))
              (Eq.trans (Eq.cong (_xor dot (N5.cod j) (d k)) (same k)) (BoolP.xor-same (dot (N5.cod j) (d k)))))))

------------------------------------------------------------------------
-- An affine circuit reading the hyperplane on the top wire

last : Bits 5 → Bool
last (_ ∷ _ ∷ _ ∷ _ ∷ b ∷ []) = b

private
  -- Wire 0 to the top: (x₀ , x₁ , x₂ , x₃ , x₄) ↦ (x₁ , x₂ , x₃ , x₄ , x₀).
  cyc : B.Circuit 5
  cyc = (B.SWAP B.↑ B.↑ B.↑) • (B.SWAP B.↑ B.↑) • (B.SWAP B.↑) • B.SWAP

  -- The transpositions of wire 0 with wire u.
  S₁ S₂ S₃ S₄ : B.Circuit 5
  S₁ = B.SWAP
  S₂ = B.SWAP • (B.SWAP B.↑) • B.SWAP
  S₃ = B.SWAP • (B.SWAP B.↑) • (B.SWAP B.↑ B.↑) • (B.SWAP B.↑) • B.SWAP
  S₄ = B.SWAP • (B.SWAP B.↑) • (B.SWAP B.↑ B.↑) • (B.SWAP B.↑ B.↑ B.↑) • (B.SWAP B.↑ B.↑) • (B.SWAP B.↑) • B.SWAP

  Xtop : Bool → B.Circuit 5
  Xtop κ = Xb (false ∷ false ∷ false ∷ false ∷ κ ∷ [])

βc : Bits 5 → Bool → B.Circuit 5
βc (true ∷ r)                              κ = Xtop κ • cyc • rowB r
βc (false ∷ true ∷ r)                      κ = Xtop κ • cyc • rowB (false ∷ r) • S₁
βc (false ∷ false ∷ true ∷ r)              κ = Xtop κ • cyc • rowB (false ∷ false ∷ r) • S₂
βc (false ∷ false ∷ false ∷ true ∷ r)      κ = Xtop κ • cyc • rowB (false ∷ false ∷ false ∷ r) • S₃
βc (false ∷ false ∷ false ∷ false ∷ true ∷ []) κ = Xtop κ • cyc • rowB (false ∷ false ∷ false ∷ false ∷ []) • S₄
βc (false ∷ false ∷ false ∷ false ∷ false ∷ []) κ = ε

private
  -- The top bit after the fan-in, the cycle and X^κ.
  top : (r : Bits 4) (κ a : Bool) (t : Bits 4) →
        last (bm (Xtop κ • cyc • rowB r) (a ∷ t)) ≡ (a xor dot r t) xor κ
  top r κ a t =
    Eq.trans (Eq.cong (λ y → last (bm (Xtop κ) (bm cyc y))) (bm-rowB r a t))
      (lst (a xor dot r t) t)
    where
    lst : ∀ (y : Bool) (t : Bits 4) → last (bm (Xtop κ) (bm cyc (y ∷ t))) ≡ y xor κ
    lst y (t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ []) =
      Eq.cong last (bm-Xb (false ∷ false ∷ false ∷ false ∷ κ ∷ []) (t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ y ∷ []))

β-top : (c : Bits 5) → c ≢ ze → ∀ κ (x : Bits 5) → last (bm (βc c κ) x) ≡ dot c x xor κ
β-top (true ∷ r) _ κ (a ∷ t) = top r κ a t
β-top (false ∷ true ∷ r) _ κ (x₀ ∷ x₁ ∷ t) = top (false ∷ r) κ x₁ (x₀ ∷ t)
β-top (false ∷ false ∷ true ∷ r) _ κ (x₀ ∷ x₁ ∷ x₂ ∷ t) = top (false ∷ false ∷ r) κ x₂ (x₁ ∷ x₀ ∷ t)
β-top (false ∷ false ∷ false ∷ true ∷ r) _ κ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ t) =
  top (false ∷ false ∷ false ∷ r) κ x₃ (x₁ ∷ x₂ ∷ x₀ ∷ t)
β-top (false ∷ false ∷ false ∷ false ∷ true ∷ []) _ κ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) =
  top (false ∷ false ∷ false ∷ false ∷ []) κ x₄ (x₁ ∷ x₂ ∷ x₃ ∷ x₀ ∷ [])
β-top (false ∷ false ∷ false ∷ false ∷ false ∷ []) nz κ x = ⊥-elim (nz refl)
