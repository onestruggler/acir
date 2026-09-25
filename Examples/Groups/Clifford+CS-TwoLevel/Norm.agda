------------------------------------------------------------------------
-- Presentations of groups
--
-- Unit vectors (§2.3).  A column v of a column-orthonormal matrix has
-- ⟨v , v⟩ = 1; writing v = w / γᵏ this says Σₓ |wₓ|² = 2ᵏ.  Hence
--
-- * Lemma "evenodd": if k > 0, an even number of the wₓ are odd;
-- * Lemma "lde0": if k = 0, exactly one wₓ is nonzero, and it is a
--   power of i.
--
-- Moreover the columns that equal standard basis vectors force the
-- other columns to vanish in their row.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Norm where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _xor_ ; _∧_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_] ; ∣_∣)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; yes ; no)

open import Instances using (adj)
open import Quantum.Synthesis.Ring
  using (Cplx ; SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)
open import Quantum.Synthesis.Ring.Properties using (adj-DComplex ; adj-ZComplex ; isCommutativeRing-DComplex)
import Quantum.Synthesis.Ring.Properties.Hom
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)
open import Quantum.Synthesis.Matrix using (Matrix)
import Data.Integer.Solver as ℤSolver

open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Scale
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
  using (_!_ ; scV ; scV-! ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count)
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics
  hiding (_!_)

private
  variable
    n : ℕ
  module ℤS = ℤSolver.+-*-Solver
  module Adjᴰ = IsInvolutiveRingEndo adj-DComplex

------------------------------------------------------------------------
-- Norms of Gaussian integers

Nℕ : Z → ℕ
Nℕ (Cplx a b) = ∣ a ∣ ℕ.* ∣ a ∣ ℕ.+ ∣ b ∣ ℕ.* ∣ b ∣

private
  sq-abs : ∀ a → a ℤ.* a ≡ + (∣ a ∣ ℕ.* ∣ a ∣)
  sq-abs (+ n) = sym (ℤP.pos-* n n)
  sq-abs -[1+ n ] = refl

-- w̄ w = |w|².
adj-mul : ∀ w → adj w ZR.* w ≡ Cplx (+ Nℕ w) (+ 0)
adj-mul (Cplx a b) = cong₂ Cplx re-eq im-eq
  where
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)
  re-eq : a ℤ.* a ℤ.+ ℤ.- ((ℤ.- b) ℤ.* b) ≡ + (∣ a ∣ ℕ.* ∣ a ∣ ℕ.+ ∣ b ∣ ℕ.* ∣ b ∣)
  re-eq = begin
    a ℤ.* a ℤ.+ ℤ.- ((ℤ.- b) ℤ.* b)       ≡⟨ ℤS.solve 2 (λ a b → a :* a :+ :- ((:- b) :* b) := a :* a :+ b :* b) refl a b ⟩
    a ℤ.* a ℤ.+ b ℤ.* b                   ≡⟨ cong₂ ℤ._+_ (sq-abs a) (sq-abs b) ⟩
    + (∣ a ∣ ℕ.* ∣ a ∣) ℤ.+ + (∣ b ∣ ℕ.* ∣ b ∣)   ≡⟨ sym (ℤP.pos-+ (∣ a ∣ ℕ.* ∣ a ∣) (∣ b ∣ ℕ.* ∣ b ∣)) ⟩
    + (∣ a ∣ ℕ.* ∣ a ∣ ℕ.+ ∣ b ∣ ℕ.* ∣ b ∣)   ∎
    where open ≡-Reasoning
  im-eq : a ℤ.* b ℤ.+ (ℤ.- b) ℤ.* a ≡ + 0
  im-eq = ℤS.solve 2 (λ a b → a :* b :+ (:- b) :* a := con (+ 0)) refl a b

-- |w|² is odd iff w is.
oddℕ-Nℕ : ∀ w → oddℕ (Nℕ w) ≡ oddᶻ w
oddℕ-Nℕ (Cplx a b) = begin
  oddℕ (∣ a ∣ ℕ.* ∣ a ∣ ℕ.+ ∣ b ∣ ℕ.* ∣ b ∣)
    ≡⟨ oddℕ-+ (∣ a ∣ ℕ.* ∣ a ∣) (∣ b ∣ ℕ.* ∣ b ∣) ⟩
  oddℕ (∣ a ∣ ℕ.* ∣ a ∣) xor oddℕ (∣ b ∣ ℕ.* ∣ b ∣)
    ≡⟨ cong₂ _xor_ (trans (oddℕ-* ∣ a ∣ ∣ a ∣) (BoolP.∧-idem (oddℕ ∣ a ∣)))
                   (trans (oddℕ-* ∣ b ∣ ∣ b ∣) (BoolP.∧-idem (oddℕ ∣ b ∣))) ⟩
  oddℤ a xor oddℤ b
    ≡⟨ sym (oddℤ-+ a b) ⟩
  oddℤ (a ℤ.+ b) ∎
  where open ≡-Reasoning

private
  N≡0 : ∀ w → Nℕ w ≡ 0 → w ≡ ZR.0#
  N≡0 (Cplx a b) eq = cong₂ Cplx (abs0 a (sq0 ∣ a ∣ (ℕP.m+n≡0⇒m≡0 _ eq)))
                                  (abs0 b (sq0 ∣ b ∣ (ℕP.m+n≡0⇒n≡0 (∣ a ∣ ℕ.* ∣ a ∣) eq)))
    where
    sq0 : ∀ m → m ℕ.* m ≡ 0 → m ≡ 0
    sq0 zero _ = refl
    abs0 : ∀ x → ∣ x ∣ ≡ 0 → x ≡ + 0
    abs0 x = ℤP.∣i∣≡0⇒i≡0

------------------------------------------------------------------------
-- Units

-- The units of ℤ[i] are the powers of i.
Unit : Z → Set
Unit u = ∃ λ t → t ℕ.< 4 × u ≡ ⅈᶻ ^ᶻ t

private
  N≡1 : ∀ w → Nℕ w ≡ 1 → Unit w
  N≡1 (Cplx (+ 0) (+ 0)) ()
  N≡1 (Cplx (+ 0) (+ 1)) _ = 1 , ℕ.s≤s (ℕ.s≤s ℕ.z≤n) , refl
  N≡1 (Cplx (+ 0) -[1+ 0 ]) _ = 3 , ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))) , refl
  N≡1 (Cplx (+ 0) (+ suc (suc m))) ()
  N≡1 (Cplx (+ 0) -[1+ suc m ]) ()
  N≡1 (Cplx (+ 1) (+ 0)) _ = 0 , ℕ.s≤s ℕ.z≤n , refl
  N≡1 (Cplx (+ 1) (+ suc m)) ()
  N≡1 (Cplx (+ 1) -[1+ m ]) ()
  N≡1 (Cplx -[1+ 0 ] (+ 0)) _ = 2 , ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) , refl
  N≡1 (Cplx -[1+ 0 ] (+ suc m)) ()
  N≡1 (Cplx -[1+ 0 ] -[1+ m ]) ()
  N≡1 (Cplx (+ suc (suc m)) b) ()
  N≡1 (Cplx -[1+ suc m ] b) ()

------------------------------------------------------------------------
-- Sums of norms

Σℕ : (Fin n → ℕ) → ℕ
Σℕ {zero} f = 0
Σℕ {suc n} f = f zero ℕ.+ Σℕ (f ∘ suc)

private
  odd-ind : ∀ b → oddℕ (if b then 1 else 0) ≡ b
  odd-ind true  = refl
  odd-ind false = refl

-- The parity of Σₓ |wₓ|² is the parity of the number of odd wₓ.
parity-count : (w : Vec Z n) →
               oddℕ (Σℕ (λ x → Nℕ (w ! x))) ≡ oddℕ (count (λ x → oddᶻ (w ! x)))
parity-count [] = refl
parity-count (z ∷ zs) = begin
  oddℕ (Nℕ z ℕ.+ Σℕ (λ x → Nℕ (zs ! x)))
    ≡⟨ oddℕ-+ (Nℕ z) (Σℕ (λ x → Nℕ (zs ! x))) ⟩
  oddℕ (Nℕ z) xor oddℕ (Σℕ (λ x → Nℕ (zs ! x)))
    ≡⟨ cong₂ _xor_ (trans (oddℕ-Nℕ z) (sym (odd-ind (oddᶻ z)))) (parity-count zs) ⟩
  oddℕ (if oddᶻ z then 1 else 0) xor oddℕ (count (λ x → oddᶻ (zs ! x)))
    ≡⟨ sym (oddℕ-+ (if oddᶻ z then 1 else 0) (count (λ x → oddᶻ (zs ! x)))) ⟩
  oddℕ ((if oddᶻ z then 1 else 0) ℕ.+ count (λ x → oddᶻ (zs ! x))) ∎
  where open ≡-Reasoning

private
  Σℕ≡0 : (f : Fin n → ℕ) → Σℕ f ≡ 0 → ∀ x → f x ≡ 0
  Σℕ≡0 {suc n} f eq zero = ℕP.m+n≡0⇒m≡0 (f zero) eq
  Σℕ≡0 {suc n} f eq (suc x) = Σℕ≡0 (f ∘ suc) (ℕP.m+n≡0⇒n≡0 (f zero) eq) x

  Σℕ≡1 : (f : Fin n → ℕ) → Σℕ f ≡ 1 → ∃ λ m → f m ≡ 1 × (∀ y → y ≢ m → f y ≡ 0)
  Σℕ≡1 {suc n} f eq with f zero in e
  ... | 0 = let (m , fm , rest) = Σℕ≡1 (f ∘ suc) eq in
            suc m , fm , λ { zero _ → e ; (suc y) y≢m → rest y (y≢m ∘ cong suc) }
  ... | 1 = zero , e , λ { zero z≢z → ⊥-elim (z≢z refl) ; (suc y) _ → Σℕ≡0 (f ∘ suc) (ℕP.suc-injective eq) y }
  ... | suc (suc m′) = ⊥-elim (big eq)
    where big : suc (suc m′) ℕ.+ Σℕ (f ∘ suc) ≢ 1
          big ()

-- Lemma "evenodd": if Σₓ |wₓ|² = 2ᵏ with k > 0, an even number of wₓ are odd.
evenodd : ∀ k (w : Vec Z n) → Σℕ (λ x → Nℕ (w ! x)) ≡ 2 ℕ.^ suc k →
          oddℕ (count (λ x → oddᶻ (w ! x))) ≡ false
evenodd k w eq = trans (sym (parity-count w)) (trans (cong oddℕ eq) (oddℕ-* 2 (2 ℕ.^ k)))

-- Lemma "lde0": if Σₓ |wₓ|² = 1, a single wₓ is nonzero, and it is a unit.
lde0 : (w : Vec Z n) → Σℕ (λ x → Nℕ (w ! x)) ≡ 1 →
       ∃ λ m → Unit (w ! m) × (∀ y → y ≢ m → w ! y ≡ ZR.0#)
lde0 w eq with Σℕ≡1 (λ x → Nℕ (w ! x)) eq
... | m , Nm , rest = m , N≡1 (w ! m) Nm , λ y y≢m → N≡0 (w ! y) (rest y y≢m)

------------------------------------------------------------------------
-- From ⟨ v , v ⟩ = 1 to Σₓ |wₓ|² = 2ᵏ

private
  adj-emb : ∀ z → adj (emb z) ≡ emb (adj z)
  adj-emb (Cplx a b) = cong (Cplx (ι₀ a)) (sym (ι₀-neg b))

  adj-^ : ∀ x k → adj (x ^ᴰ k) ≡ adj x ^ᴰ k
  adj-^ x zero = Adjᴰ.f-1
  adj-^ x (suc k) = trans (Adjᴰ.f-* x (x ^ᴰ k)) (cong (adj x DR.*_) (adj-^ x k))

  ½≡ : adj γ⁻ DR.* γ⁻ ≡ ½
  ½≡ = refl

  ½*2 : ½ DR.* emb 2ᶻ ≡ DR.1#
  ½*2 = refl

  two^≡ : ∀ N → Cplx (+ 2 ℕ.^ N) (+ 0) ≡ 2ᶻ ^ᶻ N
  two^≡ zero = refl
  two^≡ (suc N) = trans (cong₂ Cplx (trans (ℤP.pos-* 2 (2 ℕ.^ N)) (sym (ℤP.+-identityʳ (+ 2 ℤ.* + 2 ℕ.^ N)))) refl)
                        (cong (2ᶻ ZR.*_) (two^≡ N))

-- conj(w/γᵏ) · w′/γᵏ = conj(w) w′ / 2ᵏ.
adj-sc*sc : ∀ k w w′ → adj (sc k w) DR.* sc k w′ ≡ emb (adj w ZR.* w′) DR.* (½ ^ᴰ k)
adj-sc*sc k w w′ = begin
  adj (sc k w) DR.* sc k w′
    ≡⟨ cong₂ (λ a b → adj a DR.* b) (sc-def k w) (sc-def k w′) ⟩
  adj (emb w DR.* (γ⁻ ^ᴰ k)) DR.* (emb w′ DR.* (γ⁻ ^ᴰ k))
    ≡⟨ cong (DR._* (emb w′ DR.* (γ⁻ ^ᴰ k))) (Adjᴰ.f-* (emb w) (γ⁻ ^ᴰ k)) ⟩
  (adj (emb w) DR.* adj (γ⁻ ^ᴰ k)) DR.* (emb w′ DR.* (γ⁻ ^ᴰ k))
    ≡⟨ cong₂ (λ a b → (a DR.* b) DR.* (emb w′ DR.* (γ⁻ ^ᴰ k))) (adj-emb w) (adj-^ γ⁻ k) ⟩
  (emb (adj w) DR.* (adj γ⁻ ^ᴰ k)) DR.* (emb w′ DR.* (γ⁻ ^ᴰ k))
    ≡⟨ DA.*-4 (emb (adj w)) (adj γ⁻ ^ᴰ k) (emb w′) (γ⁻ ^ᴰ k) ⟩
  (emb (adj w) DR.* emb w′) DR.* ((adj γ⁻ ^ᴰ k) DR.* (γ⁻ ^ᴰ k))
    ≡⟨ cong₂ DR._*_ (sym (emb-* (adj w) w′)) (sym (DA.^-*-distrib (adj γ⁻) γ⁻ k)) ⟩
  emb (adj w ZR.* w′) DR.* ((adj γ⁻ DR.* γ⁻) ^ᴰ k)
    ≡⟨ cong (λ h → emb (adj w ZR.* w′) DR.* (h ^ᴰ k)) ½≡ ⟩
  emb (adj w ZR.* w′) DR.* (½ ^ᴰ k) ∎
  where open ≡-Reasoning

private
  C : ℕ → Z
  C m = Cplx (+ m) (+ 0)

  emb-Σ : (f : Fin n → ℕ) → sum (λ x → emb (C (f x))) ≡ emb (C (Σℕ f))
  emb-Σ {zero} f = refl
  emb-Σ {suc n} f = begin
    emb (C (f zero)) DR.+ sum (λ x → emb (C (f (suc x))))
      ≡⟨ cong (emb (C (f zero)) DR.+_) (emb-Σ (f ∘ suc)) ⟩
    emb (C (f zero)) DR.+ emb (C (Σℕ (f ∘ suc)))
      ≡⟨ sym (emb-+ (C (f zero)) (C (Σℕ (f ∘ suc)))) ⟩
    emb (C (f zero) ZR.+ C (Σℕ (f ∘ suc)))
      ≡⟨ cong emb (cong₂ Cplx (sym (ℤP.pos-+ (f zero) (Σℕ (f ∘ suc)))) refl) ⟩
    emb (C (Σℕ f)) ∎
    where open ≡-Reasoning

-- ⟨ w/γᵏ , w/γᵏ ⟩ = (Σₓ |wₓ|²) / 2ᵏ.
ip-scV : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ emb (C (Σℕ (λ x → Nℕ (w ! x)))) DR.* (½ ^ᴰ k)
ip-scV k w = begin
  sum (λ x → adj (scV k w ! x) DR.* (scV k w ! x))
    ≡⟨ sum-cong-≗ (λ x → cong (λ a → adj a DR.* a) (scV-! k w x)) ⟩
  sum (λ x → adj (sc k (w ! x)) DR.* sc k (w ! x))
    ≡⟨ sum-cong-≗ (λ x → trans (adj-sc*sc k (w ! x) (w ! x))
                               (cong (λ z → emb z DR.* (½ ^ᴰ k)) (adj-mul (w ! x)))) ⟩
  sum (λ x → emb (C (Nℕ (w ! x))) DR.* (½ ^ᴰ k))
    ≡⟨ sym (*-distribʳ-sum (½ ^ᴰ k) (λ x → emb (C (Nℕ (w ! x))))) ⟩
  sum (λ x → emb (C (Nℕ (w ! x)))) DR.* (½ ^ᴰ k)
    ≡⟨ cong (DR._* (½ ^ᴰ k)) (emb-Σ (λ x → Nℕ (w ! x))) ⟩
  emb (C (Σℕ (λ x → Nℕ (w ! x)))) DR.* (½ ^ᴰ k) ∎
  where open ≡-Reasoning

-- A unit vector w/γᵏ has Σₓ |wₓ|² = 2ᵏ.
unit-norm : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# → Σℕ (λ x → Nℕ (w ! x)) ≡ 2 ℕ.^ k
unit-norm k w eq = ℤP.+-injective (cong re (emb-injective (begin
  emb (C S)                                             ≡⟨ sym (DR.*-identityʳ (emb (C S))) ⟩
  emb (C S) DR.* DR.1#                                  ≡⟨ cong (emb (C S) DR.*_) (sym (DA.^-inverse ½ (emb 2ᶻ) k ½*2)) ⟩
  emb (C S) DR.* ((½ ^ᴰ k) DR.* (emb 2ᶻ ^ᴰ k))          ≡⟨ sym (DR.*-assoc (emb (C S)) (½ ^ᴰ k) (emb 2ᶻ ^ᴰ k)) ⟩
  (emb (C S) DR.* (½ ^ᴰ k)) DR.* (emb 2ᶻ ^ᴰ k)          ≡⟨ cong (DR._* (emb 2ᶻ ^ᴰ k)) (trans (sym (ip-scV k w)) eq) ⟩
  DR.1# DR.* (emb 2ᶻ ^ᴰ k)                              ≡⟨ DR.*-identityˡ (emb 2ᶻ ^ᴰ k) ⟩
  emb 2ᶻ ^ᴰ k                                           ≡⟨ sym (emb-^ 2ᶻ k) ⟩
  emb (2ᶻ ^ᶻ k)                                         ≡⟨ cong emb (sym (two^≡ k)) ⟩
  emb (C (2 ℕ.^ k))                                     ∎)))
  where
  open ≡-Reasoning
  S = Σℕ (λ x → Nℕ (w ! x))
  re : Z → ℤ
  re (Cplx a _) = a

